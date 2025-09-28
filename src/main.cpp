/*  DaisyMFX — consolidated sketch (Arduino + DaisyDuino + Adafruit SSD1306)
    - Banks: A Reverb, B Delay, C Mod, D Utl
    - Button: short=next (patch or preview bank), long=switch level
    - Delays: explicit tap enable, timed hand-back to knob, first-use snap
    - Safety: universal wet fade on patch change; Shimmer warm-up ramp
    - Rotary: NaN guard
    - UI: short labels (no % numerals), bars for value, instant highlight
    - Power: OLED sleep; I²C 400k when awake, 100k sleeping
*/

#include <Arduino.h>
#include <DaisyDuino.h>
#include <Wire.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <math.h>
#include <cstring>

using namespace daisysp;
using namespace daisy;

// ---------------- UI / timing ----------------
#define UI_FRAME_MIN_MS_ACTIVE  33
#define UI_FRAME_MIN_MS_IDLE    150
#define UI_ACTIVE_BOOST_MS      1500
#define UI_IDLE_SLEEP_MS        15000
#define UI_CHANGE_EPS           0.005f
#define UI_LOW_CONTRAST         0x10
#define I2C_CLOCK_HZ            100000
#define BTN_DEBOUNCE_MS         25
#define BTN_LONG_MS             800
const float OUT_LPF_HZ = 14500.f;

// ================== Hardware ==================
#define OLED_W 128
#define OLED_H 64
#define OLED_ADDR 0x3C
Adafruit_SSD1306 oled(OLED_W, OLED_H, &Wire);
const int PIN_SCL = D11, PIN_SDA = D12, PIN_BTN = D1, PIN_LED = D13;
const int PIN_POT1 = A5, PIN_POT2 = A3, PIN_POT3 = A2;
const int PIN_CV1  = A1, PIN_CV2  = A0;

// ================== DSP / utils ==================
DaisyHardware hw;
float samplerate = 48000.f;
inline float clampf(float x, float a, float b){ return x < a ? a : (x > b ? b : x); }
inline float sin01(float ph){ return sinf(2.f * 3.14159265f * ph); }
inline float map_exp01(float x01, float minv, float maxv){
  x01 = clampf(x01, 0.f, 1.f); float lnmin = logf(minv), lnrange = logf(maxv) - lnmin;
  return expf(lnmin + x01 * lnrange);
}
inline float map_lin01(float x01, float minv, float maxv){
  x01 = clampf(x01, 0.f, 1.f); return minv + x01*(maxv - minv);
}
inline void onepole_lp(float xL, float xR, float a, float &yL, float &yR){ yL += a*(xL-yL); yR += a*(xR-yR); }

// ---- Reverb core (Bank A) ----
DSY_SDRAM_BSS static ReverbSc verb;
DSY_SDRAM_BSS static DelayLine<float, 2000>  preL_A1, preR_A1;
DSY_SDRAM_BSS static DelayLine<float, 12000> preL_A2, preR_A2;
DSY_SDRAM_BSS static DelayLine<float, 16000> preL_A3, preR_A3;
DSY_SDRAM_BSS static DelayLine<float, 1200>  modL_A3, modR_A3;
float a3_phL=0.f, a3_phR; // runtime init
DSY_SDRAM_BSS static PitchShifter shifter;
DSY_SDRAM_BSS static DelayLine<float, 1200> a3mL, a3mR;
DSY_SDRAM_BSS static DelayLine<float, 1600> ghoML, ghoMR;

// ---- Delays (Bank B) ----
DSY_SDRAM_BSS static DelayLine<float, 96000> dlyL, dlyR;
float tape_ph=0.f;
float fb_lpL=0.f, fb_lpR=0.f;

// ---- Modulation (Bank C) ----
DSY_SDRAM_BSS static DelayLine<float, 3000> choL1, choR1, choL2, choR2;
DSY_SDRAM_BSS static DelayLine<float, 2000> flgL, flgR;
float ch_ph1=0.f, ch_ph2; // runtime init
float flg_ph=0.f;
struct AP1 { float a=0.f, xm1=0.f, ym1=0.f; inline float Process(float x){ float y=-a*x+xm1+a*ym1; xm1=x; ym1=y; return y; } inline void SetCoeff(float aa){ a = clampf(aa,-0.999f,0.999f);} };
AP1 phL[6], phR[6]; float ph_ph=0.f;
float rot_ph_h=0.f, rot_ph_d=0.f;
DSY_SDRAM_BSS static DelayLine<float, 1200> vbL, vbR;

// ---- Bank D (Utl) ----
DSY_SDRAM_BSS PitchShifter ps_oct_dn, ps_oct_up, ps_detL, ps_detR;
DSY_SDRAM_BSS static DelayLine<float, 2400> resDL, resDR;
float res_lpL=0.f, res_lpR=0.f;
inline float softclip_tanh(float x){ return tanhf(x); }
inline void tilt_eq(float inL,float inR,float tilt,float &outL,float &outR){
  static float lpL=0.f, lpR=0.f; float a=0.08f; lpL+=a*(inL-lpL); lpR+=a*(inR-lpR);
  float hpL=inL-lpL, hpR=inR-lpR; outL=inL+tilt*hpL-tilt*lpL; outR=inR+tilt*hpR-tilt*lpR;
}
struct SRHold { float l=0.f, r=0.f; int count=0; } srh;

// ================== Output post-filters ==================
struct DcBlock { float R, x1, y1; inline float Process(float x){ float y=x-x1+R*y1; x1=x; y1=y; return y; } } dcL, dcR;
struct OnePoleLP { float a=0.f,y=0.f; inline void SetCutoff(float fc,float fs){ float alpha=1.f-expf(-2.f*3.14159265f*fc/fs); a=clampf(alpha,0.f,1.f);} inline float Process(float x){ y+=a*(x-y); return y; } } oplpL, oplpR;

// ================== State / UI ==================
enum Bank { BANK_A, BANK_B, BANK_C, BANK_D };
enum PatchA { A1_CLASSIC, A2_PLATE, A3_TANK, A4_SHIMMER, A5_GHOST };
enum PatchB { B1_PING, B2_TAPE, B3_MULTITAP, B4_ECHOVERB, B5_FREEZE };
enum PatchC { C1_CHORUS, C2_FLANGER, C3_PHASER, C4_ROTARY, C5_VIBRATO };
enum PatchD { D1_OCTBLEND, D2_WIDENER, D3_RESONATOR, D4_DRIVE, D5_CRUSH };
enum UiLevel { LEVEL_BANK, LEVEL_PATCH };

UiLevel level; Bank bankSel; int patchIdx; Bank previewBank;
inline float readPotInv01(int pin){ return 1.f - (analogRead(pin)/65535.f); }
float P1=0, P2=0, P3=0;
inline float Adc01ToVin(float a01){ return (3.3f*a01 - 1.68f)/-0.33f; }
inline float cv_uni01(float v){ return clampf((v+5.f)*0.1f, 0.f, 1.f); }
float CV1_volts=0.f, CV2_volts=0.f, CV2_volts_raw=0.f;

struct CvTakeover { float eps_on, eps_off; bool cv_mode; bool update(float pot01){ if(!cv_mode && pot01<=eps_on) cv_mode=true; else if(cv_mode && pot01>=eps_off) cv_mode=false; return cv_mode; } } toP2, toP3;

uint32_t last_tap_ms = 0; float tap_delay_samps = 24000.f; bool tap_gate=false;
static bool g_have_tap = false; // explicit tap-tempo armed
const float TAP_HIGH=1.5f, TAP_LOW=1.0f;

bool g_oled_awake = true; uint32_t g_last_user_ms = 0;
inline void OledSleep(){ Wire.setClock(100000); if(!g_oled_awake) return; oled.ssd1306_command(SSD1306_DISPLAYOFF); g_oled_awake=false; }
inline void OledWake(){ Wire.setClock(400000); if(g_oled_awake) return; oled.ssd1306_command(SSD1306_DISPLAYON); g_oled_awake=true; }

// --- Patch/blast protection ---
static int g_patch_fade_samps = 0;
static int g_shimmer_warm_samps = 0;
static const int PATCH_FADE_SAMPS   = 2048;  // ~43 ms @ 48k
static const int SHIMMER_WARM_SAMPS = 8192;  // ~170 ms @ 48k

static void ResetFxForBankPatch(){
  verb.Init(samplerate); dlyL.Reset(); dlyR.Reset();
  fb_lpL=fb_lpR=0.f; a3_phL=0.f; a3_phR=0.5f; tape_ph=0.f; ch_ph1=0.f; ch_ph2=0.25f; flg_ph=0.f; ph_ph=0.f; rot_ph_h=0.f; rot_ph_d=0.f;
  for(int k=0;k<4000;++k){ choL1.Write(0.f); choL2.Write(0.f); choR1.Write(0.f); choR2.Write(0.f); }
  for(int k=0;k<2500;++k){ flgL.Write(0.f); flgR.Write(0.f); }
  for(int k=0;k<1300;++k){ vbL.Write(0.f); vbR.Write(0.f); }
  for(int k=0;k<2400;++k){ resDL.Write(0.f); resDR.Write(0.f); }
  res_lpL=res_lpR=0.f;

  // Arm fades
  g_patch_fade_samps = PATCH_FADE_SAMPS;
  if(bankSel == BANK_A && patchIdx == A4_SHIMMER){
    g_shimmer_warm_samps = SHIMMER_WARM_SAMPS;
    shifter.Init(samplerate);
    shifter.SetTransposition(12.f);
  } else {
    g_shimmer_warm_samps = 0;
  }
}

// ================== AUDIO CALLBACK ==================
void AudioCallback(float **in, float **out, size_t size)
{
  for(size_t i=0;i<size;i++)
  {
    float dryL=in[0][i], dryR=in[1][i];

    // Per-sample patch fade
    float patch_fade = 1.f;
    if(g_patch_fade_samps > 0){
      patch_fade = 1.f - (g_patch_fade_samps / (float)PATCH_FADE_SAMPS);
      g_patch_fade_samps--;
    }

    float wetL=dryL, wetR=dryR;
    float P2ctrl = toP2.update(P2) ? cv_uni01(CV1_volts) : P2;
    float P3ctrl = toP3.update(P3) ? cv_uni01(CV2_volts) : P3;

    if(bankSel==BANK_A){
      switch(static_cast<PatchA>(patchIdx)){
        case A1_CLASSIC:{
          float decay=map_lin01(P2ctrl,0.70f,0.98f);
          float tone =map_lin01(P3ctrl,1000.f,18000.f);
          verb.SetFeedback(decay); verb.SetLpFreq(tone);
          verb.Process(dryL,dryR,&wetL,&wetR);
        }break;

        case A2_PLATE:{
          static float pre=0.f;
          float pre_ms=map_exp01(P2ctrl,10.f,80.f);
          float target=clampf(pre_ms*0.001f*samplerate,1.f,11999.f);
          fonepole(pre,target,0.0015f);
          preL_A2.SetDelay(pre); preR_A2.SetDelay(pre);
          float inL=preL_A2.Read(), inR=preR_A2.Read();
          preL_A2.Write(dryL); preR_A2.Write(dryR);
          float tone=map_lin01(P3ctrl,12000.f,18000.f);
          float decay=map_lin01(0.6f+0.4f*P2ctrl,0.75f,0.97f);
          verb.SetFeedback(decay); verb.SetLpFreq(tone);
          verb.Process(inL,inR,&wetL,&wetR);
        }break;

        case A3_TANK:{
          static float pre=0.f;
          float pre_ms=map_exp01(P2ctrl,30.f,200.f);
          float target=clampf(pre_ms*0.001f*samplerate,1.f,15999.f);
          fonepole(pre,target,0.0015f);
          preL_A3.SetDelay(pre); preR_A3.SetDelay(pre);
          float inL=preL_A3.Read(), inR=preR_A3.Read();
          preL_A3.Write(dryL); preR_A3.Write(dryR);
          float rate=0.15f/samplerate; a3_phL+=rate; if(a3_phL>=1.f) a3_phL-=1.f;
          a3_phR+=rate; if(a3_phR>=1.f) a3_phR-=1.f;
          a3mL.SetDelay(clampf(samplerate*(0.006f+0.002f*sin01(a3_phL)),4.f,1190.f));
          a3mR.SetDelay(clampf(samplerate*(0.006f+0.002f*sin01(a3_phR+0.3f)),4.f,1190.f));
          float mmL=a3mL.Read(); a3mL.Write(inL); inL=mmL;
          float mmR=a3mR.Read(); a3mR.Write(inR); inR=mmR;
          float decay=map_lin01(0.5f+0.5f*P2ctrl,0.85f,0.985f);
          float tone =map_lin01(1.f-P3ctrl,3000.f,12000.f);
          verb.SetFeedback(decay); verb.SetLpFreq(tone);
          verb.Process(inL,inR,&wetL,&wetR);
        }break;

        case A4_SHIMMER:{
          float decay=map_lin01(P2ctrl,0.75f,0.98f);
          float tone =map_lin01(P3ctrl,1500.f,16000.f);
          verb.SetFeedback(decay); verb.SetLpFreq(tone);
          float vL,vR; verb.Process(dryL,dryR,&vL,&vR);
          float shimmer_warm = 1.f;
          if(g_shimmer_warm_samps > 0){
            shimmer_warm = 1.f - (g_shimmer_warm_samps / (float)SHIMMER_WARM_SAMPS);
            g_shimmer_warm_samps--;
          }
          float wetMono=0.5f*(vL+vR);
          float shim = shifter.Process(wetMono) * clampf(P3ctrl,0.f,1.f);
          shim *= shimmer_warm;
          wetL = vL + shim * 0.7f;
          wetR = vR + shim * 0.7f;
        }break;

        case A5_GHOST:{
          float rate=map_exp01(0.2f,0.05f,0.3f)/samplerate;
          a3_phL+=rate; if(a3_phL>=1.f)a3_phL-=1.f;
          a3_phR+=rate; if(a3_phR>=1.f)a3_phR-=1.f;
          ghoML.SetDelay(clampf(samplerate*(0.005f+0.0025f*sin01(a3_phL)),4.f,1590.f));
          ghoMR.SetDelay(clampf(samplerate*(0.005f+0.0025f*sin01(a3_phR+0.4f)),4.f,1590.f));
          float inL=ghoML.Read(), inR=ghoMR.Read();
          ghoML.Write(dryL); ghoMR.Write(dryR);
          float decay=map_lin01(P2ctrl,0.90f,0.992f);
          float tone =map_lin01(1.f-P3ctrl,800.f,8000.f);
          verb.SetFeedback(decay); verb.SetLpFreq(tone);
          verb.Process(inL,inR,&wetL,&wetR);
        }break;
      }
    }
    else if(bankSel==BANK_B){
      switch(static_cast<PatchB>(patchIdx)){
        case B1_PING:{
          static float tS=24000.f; static bool init=false;
          float targ = g_have_tap ? clampf(tap_delay_samps,10.f,95990.f)
                                  : clampf(map_exp01(P2ctrl,10.f,800.f)*0.001f*samplerate,10.f,95990.f);
          if(!init){ tS=targ; init=true; }
          fonepole(tS,targ,0.0015f);
          dlyL.SetDelay(tS); dlyR.SetDelay(tS);
          float dl=dlyL.Read(), dr=dlyR.Read();
          float fb=clampf(P3ctrl,0.f,0.90f);
          dlyL.Write(dryL + dr*fb);
          dlyR.Write(dryR + dl*fb);
          wetL=dl; wetR=dr;
        }break;

        case B2_TAPE:{
          static float tS=24000.f; static bool init=false;
          float base_ms=map_exp01(P2ctrl,20.f,800.f);
          tape_ph+=0.6f/samplerate; if(tape_ph>=1.f)tape_ph-=1.f;
          float mod=1.f+0.0025f*sin01(tape_ph);
          float targ=clampf(base_ms*mod*0.001f*samplerate,10.f,95990.f);
          if(!init){ tS=targ; init=true; }
          fonepole(tS,targ,0.0015f);
          dlyL.SetDelay(tS); dlyR.SetDelay(tS);
          float dl=dlyL.Read(), dr=dlyR.Read();
          float fbAmt=clampf(P3ctrl,0.f,0.90f);
          float tone_a=map_lin01(fbAmt,0.10f,0.35f);
          float fbL=dl, fbR=dr; onepole_lp(fbL,fbR,tone_a,fb_lpL,fb_lpR);
          dlyL.Write(dryL + fb_lpL*fbAmt);
          dlyR.Write(dryR + fb_lpR*fbAmt);
          wetL=dl; wetR=dr;
        }break;

        case B3_MULTITAP:{
          static float baseS=24000.f; static bool init=false;
          float base_ms=map_exp01(P2ctrl,60.f,900.f);
          float targ=clampf(base_ms*0.001f*samplerate,10.f,63990.f);
          if(!init){ baseS=targ; init=true; }
          fonepole(baseS,targ,0.0015f);
          dlyL.SetDelay(10.f); dlyR.SetDelay(10.f);
          dlyL.Write(dryL); dlyR.Write(dryR);
          float taps[3]={0.5f*baseS,1.0f*baseS,1.5f*baseS};
          float sumL=0.f,sumR=0.f;
          for(int t=0;t<3;t++){
            float d=clampf(taps[t],10.f,95990.f);
            dlyL.SetDelay(d); dlyR.SetDelay(d);
            float xL=dlyL.Read(), xR=dlyR.Read();
            float pan=(t-1)*clampf(P3ctrl,0.f,1.f);
            float g=clampf(1.f-0.2f*t,0.5f,1.f);
            float l=(pan<=0.f)?1.f:(1.f-pan);
            float r=(pan>=0.f)?1.f:(1.f+pan);
            sumL+=xL*g*l; sumR+=xR*g*r;
          }
          wetL=sumL; wetR=sumR;
        }break;

        case B4_ECHOVERB:{
          static float tS=24000.f; static bool init=false;
          float targ = g_have_tap ? clampf(tap_delay_samps,10.f,95990.f)
                                  : clampf(map_exp01(P2ctrl,30.f,900.f)*0.001f*samplerate,10.f,95990.f);
          if(!init){ tS=targ; init=true; }
          fonepole(tS,targ,0.0015f);
          dlyL.SetDelay(tS); dlyR.SetDelay(tS);
          float dl=dlyL.Read(), dr=dlyR.Read();
          float fb01=clampf(P3ctrl,0.f,1.f);
          float fb=clampf(fb01,0.f,0.90f);
          float tone_a=map_lin01(fb01,0.10f,0.35f);
          float fbL=dl, fbR=dr; onepole_lp(fbL,fbR,tone_a,fb_lpL,fb_lpR);
          dlyL.Write(dryL+fb_lpL*fb); dlyR.Write(dryR+fb_lpR*fb);
          float vL,vR;
          verb.SetFeedback(0.88f);
          verb.SetLpFreq(map_lin01(1.f-fb01,5000.f,14000.f));
          verb.Process(dl*map_lin01(fb01,0.20f,0.60f),
                       dr*map_lin01(fb01,0.20f,0.60f), &vL,&vR);
          wetL=dl+vL; wetR=dr+vR;
        }break;

        case B5_FREEZE:{
          static float holdS=24000.f; static bool init=false;
          float targ=clampf(map_exp01(P2ctrl,40.f,1200.f)*0.001f*samplerate,480.f,64000.f);
          if(!init){ holdS=targ; init=true; }
          fonepole(holdS,targ,0.0015f);
          dlyL.SetDelay(holdS); dlyR.SetDelay(holdS);
          float dl=dlyL.Read(), dr=dlyR.Read();
          float tone_a=map_lin01(1.f-P3ctrl,0.08f,0.35f);
          onepole_lp(dl,dr,tone_a,fb_lpL,fb_lpR);
          float mixIn=map_lin01(P2ctrl,0.15f,0.02f);
          dlyL.Write(dl*0.98f + dryL*mixIn);
          dlyR.Write(dr*0.98f + dryR*mixIn);
          wetL=dl; wetR=dr;
        }break;
      }
    }
    else if(bankSel==BANK_C){
      switch(static_cast<PatchC>(patchIdx)){
        case C1_CHORUS:{
          float rate=map_exp01(P2ctrl,0.05f,3.0f);
          float depth_ms=map_lin01(P3ctrl,2.0f,12.0f);
          float base_ms=6.0f;
          ch_ph1+=rate/samplerate; if(ch_ph1>=1.f) ch_ph1-=1.f;
          ch_ph2=ch_ph1+0.33f; if(ch_ph2>=1.f) ch_ph2-=1.f;
          float dL1=clampf((base_ms+depth_ms*sin01(ch_ph1))*0.001f*samplerate,4.f,2990.f);
          float dL2=clampf((base_ms+depth_ms*sin01(ch_ph2))*0.001f*samplerate,4.f,2990.f);
          float dR1=clampf((base_ms+depth_ms*sin01(ch_ph1+0.5f))*0.001f*samplerate,4.f,2990.f);
          float dR2=clampf((base_ms+depth_ms*sin01(ch_ph2+0.5f))*0.001f*samplerate,4.f,2990.f);
          choL1.SetDelay(dL1); choL2.SetDelay(dL2); choR1.SetDelay(dR1); choR2.SetDelay(dR2);
          float cL=0.5f*(choL1.Read()+choL2.Read());
          float cR=0.5f*(choR1.Read()+choR2.Read());
          choL1.Write(dryL); choL2.Write(dryL); choR1.Write(dryR); choR2.Write(dryR);
          wetL=cL; wetR=cR;
        }break;

        case C2_FLANGER:{
          float rate=map_exp01(P2ctrl,0.05f,1.5f);
          float min_ms=0.20f,max_ms=5.0f;
          flg_ph+=rate/samplerate; if(flg_ph>=1.f) flg_ph-=1.f;
          float d_ms=min_ms+(max_ms-min_ms)*0.5f*(1.f+sin01(flg_ph));
          float d=clampf(d_ms*0.001f*samplerate,4.f,1990.f);
          flgL.SetDelay(d); flgR.SetDelay(d);
          float dl=flgL.Read(), dr=flgR.Read();
          float fb=clampf(P3ctrl,0.f,0.90f);
          flgL.Write(dryL + dl*fb); flgR.Write(dryR + dr*fb);
          wetL=dl; wetR=dr;
        }break;

        case C3_PHASER:{
          float rate=map_exp01(P2ctrl,0.05f,1.5f);
          ph_ph+=rate/samplerate; if(ph_ph>=1.f) ph_ph-=1.f;
          float fc=map_exp01(0.5f*(1.f+sin01(ph_ph)),300.f,1800.f);
          float x=expf(-2.f*3.14159265f*fc/samplerate);
          for(int s=0;s<6;s++){ phL[s].SetCoeff(x); phR[s].SetCoeff(x); }
          float yL=dryL,yR=dryR; for(int s=0;s<6;s++){ yL=phL[s].Process(yL); yR=phR[s].Process(yR); }
          float depth=clampf(P3ctrl,0.f,0.90f);
          wetL=dryL+depth*(yL-dryL); wetR=dryR+depth*(yR-dryR);
        }break;

        case C4_ROTARY:{
          float base=map_exp01(P2ctrl,0.10f,6.0f);
          float speed_h=base, speed_d=speed_h*0.35f;
          rot_ph_h+=speed_h/samplerate; if(rot_ph_h>=1.f) rot_ph_h-=1.f;
          rot_ph_d+=speed_d/samplerate; if(rot_ph_d>=1.f) rot_ph_d-=1.f;

          static float lpfL=0.f,lpfR=0.f,hpfL=0.f,hpfR=0.f;
          if(!isfinite(lpfL) || !isfinite(lpfR) || !isfinite(hpfL) || !isfinite(hpfR)){ lpfL=lpfR=hpfL=hpfR=0.f; }

          const float a_lp=0.10f;
          lpfL+=a_lp*(dryL-lpfL); lpfR+=a_lp*(dryR-lpfR);
          hpfL=dryL-lpfL; hpfR=dryR-lpfR;

          float d_amp=0.5f+0.5f*sin01(rot_ph_d);
          float h_amp=0.5f+0.5f*sin01(rot_ph_h+0.25f);
          float depth=P3ctrl;

          float d_pan = clampf(sin01(rot_ph_d*0.5f)*2.f - 1.f, -1.f, 1.f);
          float h_pan = clampf(sin01(rot_ph_h*0.5f + 0.25f)*2.f - 1.f, -1.f, 1.f);

          auto panL=[](float x,float pan){ float l=sqrtf(fmaxf(0.f, 0.5f*(1.f-pan))); return x*l; };
          auto panR=[](float x,float pan){ float r=sqrtf(fmaxf(0.f, 0.5f*(1.f+pan))); return x*r; };

          float dL=panL(lpfL*(0.4f+0.6f*d_amp*depth), d_pan);
          float dR=panR(lpfR*(0.4f+0.6f*d_amp*depth), d_pan);
          float hL=panL(hpfL*(0.4f+0.6f*h_amp*depth), h_pan);
          float hR=panR(hpfR*(0.4f+0.6f*h_amp*depth), h_pan);

          wetL = isfinite(dL+hL) ? (dL+hL) : 0.f;
          wetR = isfinite(dR+hR) ? (dR+hR) : 0.f;
        }break;

        case C5_VIBRATO:{
          static bool init=false; if(!init){ vbL.Init(); vbR.Init(); init=true; }
          static float ph=0.f; float rate=map_exp01(P2ctrl,0.5f,8.f);
          float depth_ms=map_lin01(P3ctrl,0.5f,6.0f); float base_ms=3.0f;
          ph+=rate/samplerate; if(ph>=1.f) ph-=1.f;
          float dL=clampf((base_ms+depth_ms*sin01(ph))*0.001f*samplerate,4.f,1190.f);
          float dR=clampf((base_ms+depth_ms*sin01(ph+0.5f))*0.001f*samplerate,4.f,1190.f);
          vbL.SetDelay(dL); vbR.SetDelay(dR); float wl=vbL.Read(), wr=vbR.Read(); vbL.Write(dryL); vbR.Write(dryR);
          wetL=wl; wetR=wr;
        }break;
      }
    }
    else { // BANK_D — Utl
      switch(static_cast<PatchD>(patchIdx)){
        case D1_OCTBLEND:{
          float mono=0.5f*(dryL+dryR);
          float dn=ps_oct_dn.Process(mono), up=ps_oct_up.Process(mono);
          float b=clampf(P2ctrl,0.f,1.f); float dw=(b<0.5f)?1.f:1.f-(b-0.5f)*2.f; float uw=(b>0.5f)?1.f:b*2.f;
          float mix=(dn*dw+up*uw)*0.8f;
          float tl=mix,tr=mix; float a=map_lin01(1.f-P3ctrl,0.05f,0.35f);
          onepole_lp(tl,tr,a,fb_lpL,fb_lpR);
          wetL=tl; wetR=tr;
        }break;

        case D2_WIDENER:{
          static float ph=0.f; float cents=clampf(map_lin01(P2ctrl,0.f,20.f),0.f,50.f);
          float rate=map_lin01(P3ctrl,0.f,5.f);
          ph+=rate/samplerate; if(ph>=1.f) ph-=1.f;
          float lc=+cents*(0.5f+0.5f*sin01(ph));
          float rc=-cents*(0.5f+0.5f*sin01(ph+0.33f));
          ps_detL.SetTransposition(lc/100.f); ps_detR.SetTransposition(rc/100.f);
          wetL=ps_detL.Process(dryL); wetR=ps_detR.Process(dryR);
        }break;

        case D3_RESONATOR:{
          float midi=map_lin01(P2ctrl,36.f,84.f);
          float freq=440.f * exp2f((midi - 69.f) / 12.f);
          float dS=clampf(samplerate/freq,4.f,2300.f);
          resDL.SetDelay(dS); resDR.SetDelay(dS);
          float fb=map_lin01(1.f-P3ctrl,0.70f,0.97f);
          float rl=resDL.Read(), rr=resDR.Read();
          float a=map_lin01(P3ctrl,0.08f,0.30f);
          onepole_lp(rl,rr,a,res_lpL,res_lpR);
          resDL.Write(dryL+res_lpL*fb); resDR.Write(dryR+res_lpR*fb);
          wetL=rl; wetR=rr;
        }break;

        case D4_DRIVE:{
          float preg=map_exp01(P2ctrl,1.0f,16.0f);
          float t=map_lin01(P3ctrl,-0.6f,+0.6f);
          float inL=dryL*preg, inR=dryR*preg;
          float sL=softclip_tanh(inL), sR=softclip_tanh(inR);
          float tl,tr; tilt_eq(sL,sR,t,tl,tr);
          wetL=clampf(tl*0.8f,-1.2f,1.2f);
          wetR=clampf(tr*0.8f,-1.2f,1.2f);
        }break;

        case D5_CRUSH:{
          int maxH=24; int holdN=(int)roundf(map_lin01(P3ctrl,1.f,(float)maxH));
          if(srh.count<=0){ srh.l=dryL; srh.r=dryR; srh.count=holdN; } else { srh.count--; }
          float dsL=srh.l, dsR=srh.r;
          float bits=map_lin01(P2ctrl,16.f,4.f);
          float steps = exp2f(bits) - 1.f;
          float qL=roundf(clampf((dsL*0.5f+0.5f),0.f,1.f)*steps)/steps;
          float qR=roundf(clampf((dsR*0.5f+0.5f),0.f,1.f)*steps)/steps;
          float bcL=(qL-0.5f)*2.f, bcR=(qR-0.5f)*2.f;
          float tl=bcL,tr=bcR; float a=map_lin01(1.f-P3ctrl,0.06f,0.25f);
          onepole_lp(tl,tr,a,fb_lpL,fb_lpR);
          wetL=tl; wetR=tr;
        }break;
      }
    }

    // Apply universal patch fade (protects from first-sample slams)
    wetL *= patch_fade;
    wetR *= patch_fade;

    // Final mix + output filtering
    float outL=(1.f-P1)*dryL + P1*wetL;
    float outR=(1.f-P1)*dryR + P1*wetR;
    outL = dcL.Process(outL); outR = dcR.Process(outR);
    outL = oplpL.Process(outL); outR = oplpR.Process(outR);
    outL = clampf(outL,-1.2f,1.2f); outR = clampf(outR,-1.2f,1.2f);
    out[0][i]=outL; out[1][i]=outR;
  }
}

// ================== OLED (helpers) ==================
namespace ui {
static void printClipped(int x,int y,int w,const char* s){ int maxChars=(w-10)/6; if(maxChars<=0) return; int n=0; while(s[n]&&n<maxChars) n++; char buf[32]; if(n>= (int)sizeof(buf)) n=sizeof(buf)-1; memcpy(buf,s,n); buf[n]=0; oled.setCursor(x,y); oled.print(buf); }
static void printClippedBold(int x,int y,int w,const char* s,bool bold){ int maxChars=(w-10)/6; if(maxChars<=0) return; int n=0; while(s[n]&&n<maxChars) n++; char buf[32]; if(n>= (int)sizeof(buf)) n=sizeof(buf)-1; memcpy(buf,s,n); buf[n]=0; oled.setCursor(x,y); oled.print(buf); if(bold){ oled.setCursor(x+1,y); oled.print(buf);} }
static void drawBar(int x,int y,int w,int h,float amt,bool invert=false){ amt=clampf(amt,0.f,1.f); int fill=(int)((w-2)*amt+0.5f); if(invert) oled.fillRect(x,y,w,h,SSD1306_WHITE); oled.drawRect(x,y,w,h,SSD1306_WHITE); if(fill>0) oled.fillRect(x+1,y+1,fill,h-2,invert?SSD1306_BLACK:SSD1306_WHITE); }

// Label-only printer (no numerals)
static void printLabelOnly(int x,int y,int w,const char* label){
  int maxChars=(w-10)/6; if(maxChars<=0) return;
  int n=0; while(label[n] && n<maxChars) n++;
  char buf[24]; if(n >= (int)sizeof(buf)) n = sizeof(buf)-1;
  memcpy(buf,label,n); buf[n]=0;
  oled.setCursor(x,y); oled.print(buf);
}

static const char* GetBankTitle(Bank b){
  switch(b){
    case BANK_A: return "A: Revb";
    case BANK_B: return "B: Dely";
    case BANK_C: return "C: Mods";
    case BANK_D: return "D: Util";
  }
  return "(?)";
}

static const char* patchTitleShort(){
  if(bankSel==BANK_A){ switch(static_cast<PatchA>(patchIdx)){
    case A1_CLASSIC:   return "A1 Classic";
    case A2_PLATE:     return "A2 Plate";
    case A3_TANK:      return "A3 Tank";
    case A4_SHIMMER:   return "A4 Shimmer";
    case A5_GHOST:     return "A5 Ghost"; } }
  else if(bankSel==BANK_B){ switch(static_cast<PatchB>(patchIdx)){
    case B1_PING:      return "B1 Ping";
    case B2_TAPE:      return "B2 Tape";
    case B3_MULTITAP:  return "B3 MultiTap";
    case B4_ECHOVERB:  return "B4 Echo";
    case B5_FREEZE:    return "B5 Freeze"; } }
  else if(bankSel==BANK_C){ switch(static_cast<PatchC>(patchIdx)){
    case C1_CHORUS:    return "C1 Chorus";
    case C2_FLANGER:   return "C2 Flanger";
    case C3_PHASER:    return "C3 Phaser";
    case C4_ROTARY:    return "C4 Rotary";
    case C5_VIBRATO:   return "C5 Vibrato"; } }
  else { switch(static_cast<PatchD>(patchIdx)){
    case D1_OCTBLEND:  return "D1 Octave";
    case D2_WIDENER:   return "D2 Wide";
    case D3_RESONATOR: return "D3 Resonator";
    case D4_DRIVE:     return "D4 Drive";
    case D5_CRUSH:     return "D5 Crush"; } }
  return "";
}

// ---- 3–4 char parameter labels ----
static const char* p1Label() { return "Mix"; }
static const char* p2Label() {
  if(bankSel==BANK_A){
    switch(static_cast<PatchA>(patchIdx)){ case A2_PLATE: case A3_TANK: return "PreD"; default: return "Decy"; }
  } else if(bankSel==BANK_B){
    switch(static_cast<PatchB>(patchIdx)){ case B5_FREEZE: return "Size"; default: return "Time"; }
  } else if(bankSel==BANK_C){
    return "Rate";
  } else {
    switch(static_cast<PatchD>(patchIdx)){
      case D1_OCTBLEND:  return "Blen";
      case D2_WIDENER:   return "Detn";
      case D3_RESONATOR: return "Pitc";
      case D4_DRIVE:     return "Gain";
      case D5_CRUSH:     return "Bits";
    }
  }
  return "P2";
}
static const char* p3Label() {
  if(bankSel==BANK_A){
    return (patchIdx==A4_SHIMMER) ? "Shim" : "Tone";
  } else if(bankSel==BANK_B){
    return (patchIdx==B4_ECHOVERB) ? "Macr" : "Fdbk";
  } else if(bankSel==BANK_C){
    return "Dept";
  } else {
    switch(static_cast<PatchD>(patchIdx)){
      case D1_OCTBLEND:  return "Tone";
      case D2_WIDENER:   return "Rate";
      case D3_RESONATOR: return "Damp";
      case D4_DRIVE:     return "Tilt";
      case D5_CRUSH:     return "Hold";
    }
  }
  return "P3";
}

static void drawBankMenu(Bank highlight){
  oled.clearDisplay(); oled.setTextSize(1); oled.setTextColor(SSD1306_WHITE);
  oled.fillRect(0,0,OLED_W,12,SSD1306_WHITE); oled.setTextColor(SSD1306_BLACK);
  ui::printClipped(2,2,OLED_W-4,"Bank Sel");
  oled.setTextColor(SSD1306_WHITE);
  int cellW=OLED_W/2, cellH=(OLED_H-12)/2; int xL=0,xR=cellW; int y1=12,y2=12+cellH;
  auto cell=[&](int x,int y,const char* label,bool hilite){ oled.drawRect(x,y,cellW,cellH,SSD1306_WHITE); int tx=x+6, ty=y+cellH/2-4; ui::printClippedBold(tx,ty,cellW-12,label,hilite); };
  cell(xL,y1,GetBankTitle(BANK_A),highlight==BANK_A);
  cell(xR,y1,GetBankTitle(BANK_B),highlight==BANK_B);
  cell(xL,y2,GetBankTitle(BANK_C),highlight==BANK_C);
  cell(xR,y2,GetBankTitle(BANK_D),highlight==BANK_D);
  oled.display();
}

static void drawPatchUi(bool btn_pressed,bool /*showTapFlag*/){
  oled.clearDisplay(); oled.setTextSize(1);
  oled.fillRect(0,0,OLED_W,12,SSD1306_WHITE);
  oled.setTextColor(SSD1306_BLACK);
  ui::printClipped(2,2,96,patchTitleShort());
  oled.setTextColor(SSD1306_WHITE);

  const int yRow1=14,yRow2=38; const int cellW_L=60,cellW_R=68,cellH=22;

  // Button cell
  oled.drawRect(0,yRow1,cellW_L,cellH,SSD1306_WHITE);
  ui::printClipped(4,yRow1+2,cellW_L-8,"Btn");
  ui::drawBar(4,yRow1+cellH-9,cellW_L-8,7,btn_pressed?1.f:0.f);

  // P1
  oled.drawRect(cellW_L,yRow1,cellW_R,cellH,SSD1306_WHITE);
  ui::printLabelOnly(cellW_L+4,yRow1+2,cellW_R-8,ui::p1Label());
  ui::drawBar(cellW_L+4,yRow1+cellH-9,cellW_R-8,7,P1);

  // P2
  oled.drawRect(0,yRow2,cellW_L,cellH,SSD1306_WHITE);
  ui::printLabelOnly(4,yRow2+2,cellW_L-8,ui::p2Label());
  ui::drawBar(4,yRow2+cellH-9,cellW_L-8,7,(toP2.cv_mode?cv_uni01(CV1_volts):P2),toP2.cv_mode);

  // P3
  oled.drawRect(cellW_L,yRow2,cellW_R,cellH,SSD1306_WHITE);
  ui::printLabelOnly(cellW_L+4,yRow2+2,cellW_R-8,ui::p3Label());
  ui::drawBar(cellW_L+4,yRow2+cellH-9,cellW_R-8,7,(toP3.cv_mode?cv_uni01(CV2_volts):P3),toP3.cv_mode);

  oled.display();
}
} // namespace ui

// ================== SETUP / LOOP ==================
void setup(){
  Serial.begin(115200); uint32_t t0=millis(); while(!Serial && (millis()-t0)<1500) {}
  hw = DAISY.init(DAISY_PATCH, AUDIO_SR_48K); samplerate = DAISY.get_samplerate(); analogReadResolution(16);
  Wire.setSCL(PIN_SCL); Wire.setSDA(PIN_SDA); Wire.begin(); Wire.setClock(I2C_CLOCK_HZ);
  pinMode(PIN_BTN,INPUT_PULLUP); pinMode(PIN_LED,OUTPUT);
  if(!oled.begin(SSD1306_SWITCHCAPVCC, OLED_ADDR)){ for(;;){ digitalWrite(PIN_LED,!digitalRead(PIN_LED)); delay(150);} }
  oled.dim(true); oled.ssd1306_command(SSD1306_SETCONTRAST); oled.ssd1306_command(UI_LOW_CONTRAST);

  verb.Init(samplerate); preL_A1.Init(); preR_A1.Init(); preL_A2.Init(); preR_A2.Init(); preL_A3.Init(); preR_A3.Init(); modL_A3.Init(); modR_A3.Init();
  shifter.Init(samplerate); shifter.SetTransposition(12.f);
  dlyL.Init(); dlyR.Init(); choL1.Init(); choL2.Init(); choR1.Init(); choR2.Init(); flgL.Init(); flgR.Init();
  a3mL.Init(); a3mR.Init(); ghoML.Init(); ghoMR.Init(); vbL.Init(); vbR.Init();
  ps_oct_dn.Init(samplerate); ps_oct_up.Init(samplerate); ps_detL.Init(samplerate); ps_detR.Init(samplerate);
  ps_oct_dn.SetTransposition(-12.f); ps_oct_up.SetTransposition(+12.f); ps_detL.SetTransposition(0.f); ps_detR.SetTransposition(0.f);
  resDL.Init(); resDR.Init();
  oplpL.SetCutoff(OUT_LPF_HZ,samplerate); oplpR.SetCutoff(OUT_LPF_HZ,samplerate);

  // runtime inits
  a3_phR=0.5f; ch_ph2=0.25f;
  toP2.eps_on=0.015f; toP2.eps_off=0.030f; toP2.cv_mode=false;
  toP3.eps_on=0.015f; toP3.eps_off=0.030f; toP3.cv_mode=false;
  dcL.R=dcR.R=0.995f; dcL.x1=dcL.y1=dcR.x1=dcR.y1=0.f;
  level=LEVEL_PATCH; bankSel=BANK_A; patchIdx=0; previewBank=BANK_A;

  ui::drawBankMenu(previewBank); g_last_user_ms = millis();
  DAISY.begin(AudioCallback);
}

void loop(){
  digitalWrite(PIN_LED,(millis()/500)%2);

  // Pots (smoothed)
  P1=0.98f*P1+0.02f*readPotInv01(PIN_POT1);
  P2=0.98f*P2+0.02f*readPotInv01(PIN_POT2);
  P3=0.98f*P3+0.02f*readPotInv01(PIN_POT3);

  // CV (smoothed) + raw
  float cv1_a01=analogRead(PIN_CV1)/65535.f, cv2_a01=analogRead(PIN_CV2)/65535.f;
  float cv1_v=Adc01ToVin(cv1_a01), cv2_v=Adc01ToVin(cv2_a01);
  CV1_volts=0.95f*CV1_volts+0.05f*cv1_v; CV2_volts=0.90f*CV2_volts+0.10f*cv2_v; CV2_volts_raw=cv2_v;

  uint32_t nowTicks=daisy::System::GetNow(); uint32_t ms=millis();

  // Tap-tempo on CV2 (Delays only) — explicit arm + auto hand-back
  if(bankSel==BANK_B){
    if(!tap_gate && CV2_volts_raw>=TAP_HIGH){
      tap_gate=true;
      uint32_t dt=nowTicks-last_tap_ms;
      if(dt>50 && dt<2000){
        tap_delay_samps=(dt/1000.f)*samplerate;
        g_have_tap = true;
      }
      last_tap_ms=nowTicks;
    } else if(tap_gate && CV2_volts_raw<=TAP_LOW){
      tap_gate=false;
    }
    // auto-disarm so knob resumes control
    if(g_have_tap && (nowTicks - last_tap_ms) > 1800){
      g_have_tap = false;
    }
  } else {
    g_have_tap = false; // leaving delay bank cancels tap
  }

  // Button (debounced, short/long)
  static bool btn_state=false, btn_last=false, btn_long_fired=false;
  static uint32_t btn_last_change_ms=0, btn_press_start_ms=0;
  bool raw_pressed=(digitalRead(PIN_BTN)==LOW);
  if(raw_pressed!=btn_last){ btn_last=raw_pressed; btn_last_change_ms=ms; }
  if(ms-btn_last_change_ms>=BTN_DEBOUNCE_MS && btn_state!=raw_pressed){
    btn_state=raw_pressed;
    if(btn_state){ btn_press_start_ms=ms; btn_long_fired=false; g_last_user_ms=ms; OledWake(); }
    else if(!btn_long_fired){
      if(level==LEVEL_BANK){ previewBank=(Bank)((((int)previewBank)+1)%4); }
      else { patchIdx=(patchIdx+1)%5; ResetFxForBankPatch(); }
      g_last_user_ms=ms; OledWake();
    }
  }
  if(btn_state && !btn_long_fired && (ms-btn_press_start_ms>=BTN_LONG_MS)){
    btn_long_fired=true;
    if(level==LEVEL_BANK){ bankSel=previewBank; patchIdx=0; ResetFxForBankPatch(); level=LEVEL_PATCH; }
    else { previewBank=bankSel; level=LEVEL_BANK; }
    g_last_user_ms=ms; OledWake();
  }

  // Event-driven UI
  static uint32_t last_draw=0;
  static float p1_last=-1.f,p2_last=-1.f,p3_last=-1.f;
  static int patch_last=-1; static Bank bank_last=(Bank)255, preview_last=(Bank)255;
  static UiLevel level_last=(UiLevel)255;
  bool showTap=(bankSel==BANK_B)&&((nowTicks-last_tap_ms)<200); // only for redraw sensitivity

  bool user_interaction = btn_state
    || fabsf(P1-p1_last)>UI_CHANGE_EPS || fabsf(P2-p2_last)>UI_CHANGE_EPS || fabsf(P3-p3_last)>UI_CHANGE_EPS
    || (patchIdx!=patch_last) || (bankSel!=bank_last) || (previewBank!=preview_last) || (level!=level_last) || showTap;

  if(user_interaction){ g_last_user_ms=ms; OledWake(); }
  if(ms-g_last_user_ms>UI_IDLE_SLEEP_MS){ OledSleep(); }

  uint32_t min_frame = (ms-g_last_user_ms)<UI_ACTIVE_BOOST_MS ? UI_FRAME_MIN_MS_ACTIVE : UI_FRAME_MIN_MS_IDLE;
  if(g_oled_awake && (ms-last_draw)>=min_frame && user_interaction){
    last_draw=ms; p1_last=P1; p2_last=P2; p3_last=P3; patch_last=patchIdx; bank_last=bankSel; preview_last=previewBank; level_last=level;
    if(level==LEVEL_BANK) ui::drawBankMenu(previewBank); else ui::drawPatchUi(btn_state,showTap);
  }
}

