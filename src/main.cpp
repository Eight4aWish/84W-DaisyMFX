/*
  DaisyMFX — full sketch (Arduino + DaisyDuino + Adafruit SSD1306)

  - 4 banks * 5 patches = 20 FX
  - UI highlight now same size with faux-bold (no big-font flooding)
  - Bank D granular: simple, CPU-light implementations designed for reliability
  - OLED noise mitigation:
      * Event-driven redraw (throttled)
      * Low contrast / dim
      * Auto-sleep after inactivity
      * Slower I2C clock by default (100 kHz)

  Serial monitor @ 115200 (USB CDC)
*/

#include <Arduino.h>
#include <DaisyDuino.h>
#include <Wire.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <math.h>
#include <cstring> // memcpy

using namespace daisysp;
using namespace daisy;

// ---------------- UI Noise Mitigation Settings ----------------
#define UI_FRAME_MIN_MS         150    // cap to <= ~6–7 FPS
#define UI_IDLE_SLEEP_MS        15000  // OLED off after 15 s idle
#define UI_CHANGE_EPS           0.02f  // redraw if any control changes >2%
#define UI_LOW_CONTRAST         0x10   // 0..255 (SSD1306 native contrast)
#define I2C_CLOCK_HZ            100000 // 100 kHz (try 400000 if layout is clean)
// ----------------------------------------------------------------

// ================== Hardware ==================
#define OLED_W 128
#define OLED_H 64
#define OLED_ADDR 0x3C
Adafruit_SSD1306 oled(OLED_W, OLED_H, &Wire);

const int PIN_SCL = D11;     // I2C1 SCL
const int PIN_SDA = D12;     // I2C1 SDA
const int PIN_BTN = D1;      // button -> GND (INPUT_PULLUP)
const int PIN_LED = D13;     // onboard LED

// Pots (CW = max)
const int PIN_POT1 = A5;     // P1 Mix
const int PIN_POT2 = A3;     // P2 Time/Rate/Pre/Size  (CV1 takeover)
const int PIN_POT3 = A2;     // P3 FB/Depth/Tone       (CV2 takeover)

// CVs (your -5..+5 → 3.3..0 V mapping)
const int PIN_CV1  = A1;     // takeover for P2
const int PIN_CV2  = A0;     // takeover for P3 (+ tap edges on delays)

// ================== DSP ==================
DaisyHardware hw;
float samplerate = 48000.f;

inline float clampf(float x, float a, float b){ return x < a ? a : (x > b ? b : x); }
inline float sin01(float ph){ return sinf(2.f * 3.14159265f * ph); }
inline float map_exp01(float x01, float minv, float maxv){
  x01 = clampf(x01, 0.f, 1.f);
  float lnmin = logf(minv), lnrange = logf(maxv) - lnmin;
  return expf(lnmin + x01 * lnrange);
}
inline float map_lin01(float x01, float minv, float maxv){
  x01 = clampf(x01, 0.f, 1.f);
  return minv + x01*(maxv - minv);
}

// ---- Reverb core (Bank A) ----
DSY_SDRAM_BSS static ReverbSc verb;
DSY_SDRAM_BSS static DelayLine<float, 2000>  preL_A1, preR_A1;      // ~40ms
DSY_SDRAM_BSS static DelayLine<float, 12000> preL_A2, preR_A2;      // ~80ms
DSY_SDRAM_BSS static DelayLine<float, 16000> preL_A3, preR_A3;      // ~200ms
DSY_SDRAM_BSS static DelayLine<float, 1200>  modL_A3, modR_A3;      // ~25ms (moved to SDRAM)
float a3_phL=0.f, a3_phR=0.5f;
DSY_SDRAM_BSS static PitchShifter shifter; // A4 shimmer (in SDRAM)

// Extra mod delays for A3/A5 that were previously local (move to SDRAM)
DSY_SDRAM_BSS static DelayLine<float, 1200> a3mL, a3mR;   // A3_TANK chorus-y modulation
DSY_SDRAM_BSS static DelayLine<float, 1600> ghoML, ghoMR; // A5_GHOST subtle modulation

// ---- Delays (Bank B) ----
DSY_SDRAM_BSS static DelayLine<float, 96000> dlyL, dlyR; // up to ~2s @ 48k
float tape_ph=0.f;                // wow LFO
float fb_lpL=0.f, fb_lpR=0.f;
inline void onepole_lp(float xL, float xR, float a, float &yL, float &yR){
  yL += a * (xL - yL);
  yR += a * (xR - yR);
}

// ---- Modulation (Bank C) ----
DSY_SDRAM_BSS static DelayLine<float, 3000> choL1, choR1, choL2, choR2; // moved to SDRAM
DSY_SDRAM_BSS static DelayLine<float, 2000> flgL, flgR;                 // moved to SDRAM
float ch_ph1=0.f, ch_ph2=0.25f;

float flg_ph=0.f;

struct AP1 {
  float a=0.f, xm1=0.f, ym1=0.f;
  inline float Process(float x){
    float y = -a * x + xm1 + a * ym1;
    xm1 = x; ym1 = y;
    return y;
  }
  inline void SetCoeff(float aa){ a = clampf(aa, -0.999f, 0.999f); }
};
AP1 phL[6], phR[6];
float ph_ph = 0.f; // LFO phase

float rot_ph_h=0.f, rot_ph_d=0.f;

// Vibrato delay lines (were local; move to SDRAM)
DSY_SDRAM_BSS static DelayLine<float, 1200> vbL, vbR;

// ---- Granular (Bank D) simplistic engine pieces ----
const size_t GRBUF_SAMPS = 262144; // ~5.46s @48k (per channel), SDRAM
DSY_SDRAM_BSS static float grL[GRBUF_SAMPS];
DSY_SDRAM_BSS static float grR[GRBUF_SAMPS];
volatile uint32_t gr_write = 0;

inline float read_wrap(const float* b, size_t n, float idx)
{
  // linear interpolation with wrap
  if(idx < 0.f) idx += n * (1.f + floorf(-idx / (float)n));
  idx = fmodf(idx, (float)n);
  int i0 = (int)idx;
  int i1 = (i0 + 1) % (int)n;
  float a = idx - (float)i0;
  return b[i0] + a * (b[i1] - b[i0]);
}

// D1 MicroLoop
struct MicroLoop {
  float loop_len_samp = 4800.f; // 100ms default
  float read_posL = 0.f, read_posR = 0.f;
  float rate = 1.f;
  float xfade=0.f;
} ml;

// D2 TimeStretch (rate 0.5..2x)
struct TimeStretch {
  float rate = 1.f;
  float readL=0.f, readR=0.f;
} ts;

// D3 PitchCloud — 3x pitch shifters blended
DSY_SDRAM_BSS PitchShifter pc1, pc2, pc3;

// D4 Reverse — windowed reverse playback
struct ReverseGrain {
  uint32_t win = 12000; // 250ms
  float read = 0.f;
  float ph = 0.f; // 0..1 window pos
} revg;

// D5 Texture — random micro grains
struct Texture {
  float ph=0.f;
  float trig_rate = 40.f; // grains/s
  float gposL=0.f, gposR=0.f;
  float glen=2400.f; // 50ms
  float gph=1.f;
  float pan=0.f;
} tex;

// ================== Output post-filters ==================
struct DcBlock {
  float R=0.995f, x1=0.f, y1=0.f;
  inline float Process(float x){
    float y = x - x1 + R*y1;
    x1 = x; y1 = y;
    return y;
  }
} dcL, dcR;

struct OnePoleLP {
  float a=0.f, y=0.f;
  inline void SetCutoff(float fc, float fs){
    float alpha = 1.f - expf(-2.f * 3.14159265f * fc / fs);
    a = clampf(alpha, 0.f, 1.f);
  }
  inline float Process(float x){ y += a * (x - y); return y; }
} oplpL, oplpR;

// ================== State / UI ==================
enum Bank { BANK_A, BANK_B, BANK_C, BANK_D };
enum PatchA { A1_CLASSIC, A2_PLATE, A3_TANK, A4_SHIMMER, A5_GHOST };
enum PatchB { B1_PING, B2_TAPE, B3_MULTITAP, B4_ECHOVERB, B5_FREEZE };
enum PatchC { C1_CHORUS, C2_FLANGER, C3_PHASER, C4_ROTARY, C5_VIBRATO };
enum PatchD { D1_MICROLOOP, D2_TIMESTRETCH, D3_PITCHCLOUD, D4_REVERSE, D5_TEXTURE };
enum UiLevel { LEVEL_BANK, LEVEL_PATCH };

UiLevel level = LEVEL_PATCH;

Bank bankSel = BANK_A;
int  patchIdx = 0;            // 0..4 within the active bank
Bank previewBank = BANK_A;     // highlight on bank menu

static inline int PatchesInBank(Bank){ return 5; }

inline float readPotInv01(int pin) { return 1.f - (analogRead(pin) / 65535.f); }
float P1=0, P2=0, P3=0;

// CV calibration: Vin = (3.3*adc01 - 1.68)/-0.33  ⇒ approx -5..+5 V
inline float Adc01ToVin(float a01) { return (3.3f*a01 - 1.68f) / -0.33f; }
inline float cv_uni01(float v){ return clampf((v + 5.f) * 0.1f, 0.f, 1.f); }

float CV1_volts = 0.f, CV2_volts = 0.f;   // smoothed
float CV2_volts_raw = 0.f;                // raw for tap edges (Delays only)

struct CvTakeover {
  float eps_on  = 0.015f; // 1.5%
  float eps_off = 0.030f; // 3.0%
  bool  cv_mode = false;
  bool update(float pot01){
    if(!cv_mode && pot01 <= eps_on) cv_mode = true;
    else if(cv_mode && pot01 >= eps_off) cv_mode = false;
    return cv_mode;
  }
} toP2, toP3;

// Button handling (navigation only)
bool btn_prev=false;
uint32_t btn_down_ms=0;

// Tap-tempo for delays (CV2 edges only)
uint32_t last_tap_ms = 0;
float    tap_delay_samps = 24000.f; // ~500ms default
bool     tap_gate=false;
const float TAP_HIGH = 1.5f; // volts
const float TAP_LOW  = 1.0f;

// ---------- OLED sleep/wake helper ----------
bool g_oled_awake = true;
uint32_t g_last_user_ms = 0;

inline void OledSleep(){
  if(!g_oled_awake) return;
  oled.ssd1306_command(SSD1306_DISPLAYOFF); // 0xAE
  g_oled_awake = false;
}
inline void OledWake(){
  if(g_oled_awake) return;
  oled.ssd1306_command(SSD1306_DISPLAYON);  // 0xAF
  g_oled_awake = true;
}

// ================== AUDIO CALLBACK ==================
void AudioCallback(float **in, float **out, size_t size)
{
  for(size_t i=0;i<size;i++)
  {
    float dryL = in[0][i];
    float dryR = in[1][i];

    // ring buffer write for granular bank (always running, cheap)
    grL[gr_write] = dryL;
    grR[gr_write] = dryR;
    uint32_t wr = gr_write;
    gr_write = (gr_write + 1) % GRBUF_SAMPS;

    // effect results:
    float wetL = dryL, wetR = dryR; // init to dry so we can always mix
    float mixAmt = P1;              // default mix

    // CV takeover decisions (consistent)
    bool p2_cv = toP2.update(P2);
    bool p3_cv = toP3.update(P3);
    float P2ctrl = p2_cv ? cv_uni01(CV1_volts) : P2;  // time/rate/size
    float P3ctrl = p3_cv ? cv_uni01(CV2_volts) : P3;  // feedback/depth/tone

    if(bankSel == BANK_A)
    {
      switch(static_cast<PatchA>(patchIdx))
      {
        case A1_CLASSIC: {
          float decay  = map_lin01(P2ctrl, 0.70f, 0.98f);
          float toneHz = map_lin01(P3ctrl, 1000.f, 18000.f);
          verb.SetFeedback(decay);
          verb.SetLpFreq(toneHz);
          verb.Process(dryL, dryR, &wetL, &wetR);
        } break;

        case A2_PLATE: {
          static float pre_samp=0.f;
          float pre_ms = map_exp01(P2ctrl, 10.f, 80.f);
          float target = clampf(pre_ms*0.001f*samplerate, 1.f, 11999.f);
          fonepole(pre_samp, target, 0.0015f);
          preL_A2.SetDelay(pre_samp); preR_A2.SetDelay(pre_samp);
          float inL = preL_A2.Read(), inR = preR_A2.Read();
          preL_A2.Write(dryL); preR_A2.Write(dryR);
          float toneHz = map_lin01(P3ctrl, 12000.f, 18000.f);
          float decay  = map_lin01(0.6f + 0.4f*P2ctrl, 0.75f, 0.97f);
          verb.SetFeedback(decay);
          verb.SetLpFreq(toneHz);
          verb.Process(inL, inR, &wetL, &wetR);
        } break;

        case A3_TANK: {
          static float pre_samp=0.f;
          float pre_ms = map_exp01(P2ctrl, 30.f, 200.f);
          float target = clampf(pre_ms*0.001f*samplerate, 1.f, 15999.f);
          fonepole(pre_samp, target, 0.0015f);
          preL_A3.SetDelay(pre_samp); preR_A3.SetDelay(pre_samp);
          float inL = preL_A3.Read(), inR = preR_A3.Read();
          preL_A3.Write(dryL); preR_A3.Write(dryR);

          float rate = 0.15f / samplerate;
          a3_phL += rate; if(a3_phL>=1.f) a3_phL -= 1.f;
          a3_phR += rate; if(a3_phR>=1.f) a3_phR -= 1.f;
          a3mL.SetDelay(clampf(samplerate*(0.006f + 0.002f * sin01(a3_phL)), 4.f, 1190.f));
          a3mR.SetDelay(clampf(samplerate*(0.006f + 0.002f * sin01(a3_phR + 0.3f)), 4.f, 1190.f));
          float mmL = a3mL.Read(); a3mL.Write(inL); inL = mmL;
          float mmR = a3mR.Read(); a3mR.Write(inR); inR = mmR;

          float decay  = map_lin01(0.5f + 0.5f*P2ctrl, 0.85f, 0.985f);
          float toneHz = map_lin01(1.f - P3ctrl, 3000.f, 12000.f);
          verb.SetFeedback(decay);
          verb.SetLpFreq(toneHz);
          verb.Process(inL, inR, &wetL, &wetR);
        } break;

        case A4_SHIMMER: {
          float decay  = map_lin01(P2ctrl, 0.75f, 0.98f);
          float toneHz = map_lin01(P3ctrl, 1500.f, 16000.f);
          verb.SetFeedback(decay);
          verb.SetLpFreq(toneHz);
          float vL, vR; verb.Process(dryL, dryR, &vL, &vR);
          float wetMono = 0.5f*(vL + vR);
          float shim = shifter.Process(wetMono) * clampf(P3ctrl, 0.f, 1.f);
          wetL = vL + shim * 0.7f;
          wetR = vR + shim * 0.7f;
        } break;

        case A5_GHOST: {
          // darker, longer decay with subtle modulation (global SDRAM delays)
          float rate = map_exp01(0.2f, 0.05f, 0.3f) / samplerate;
          a3_phL += rate; if(a3_phL>=1.f) a3_phL -= 1.f;
          a3_phR += rate; if(a3_phR>=1.f) a3_phR -= 1.f;
          ghoML.SetDelay(clampf(samplerate*(0.005f + 0.0025f * sin01(a3_phL)), 4.f, 1590.f));
          ghoMR.SetDelay(clampf(samplerate*(0.005f + 0.0025f * sin01(a3_phR + 0.4f)), 4.f, 1590.f));
          float inL = ghoML.Read(); float inR = ghoMR.Read();
          ghoML.Write(dryL); ghoMR.Write(dryR);
          float decay  = map_lin01(P2ctrl, 0.90f, 0.992f);
          float toneHz = map_lin01(1.f - P3ctrl, 800.f, 8000.f);
          verb.SetFeedback(decay);
          verb.SetLpFreq(toneHz);
          verb.Process(inL, inR, &wetL, &wetR);
        } break;
      }
    }
    else if(bankSel == BANK_B)
    {
      switch(static_cast<PatchB>(patchIdx))
      {
        case B1_PING:
        {
          static float smooth_time = 24000.f; // samples
          uint32_t now = daisy::System::GetNow();
          bool recent_tap = (now - last_tap_ms) < 2000;
          float target_samps;
          if(recent_tap) target_samps = clampf(tap_delay_samps, 10.f, 95990.f);
          else           target_samps = clampf(map_exp01(P2ctrl, 10.f, 800.f) * 0.001f * samplerate, 10.f, 95990.f);
          fonepole(smooth_time, target_samps, 0.0015f);
          dlyL.SetDelay(smooth_time);
          dlyR.SetDelay(smooth_time);
          float dl = dlyL.Read();
          float dr = dlyR.Read();
          float fb = clampf(P3ctrl, 0.f, 0.90f);
          dlyL.Write(dryL + dr * fb);
          dlyR.Write(dryR + dl * fb);
          wetL = dl; wetR = dr;
        } break;

        case B2_TAPE:
        {
          static float smooth_time=24000.f;
          float base_ms = map_exp01(P2ctrl, 20.f, 800.f);
          tape_ph += 0.6f / samplerate; if(tape_ph >= 1.f) tape_ph -= 1.f;
          float mod = 1.f + 0.0025f * sin01(tape_ph); // ~±0.25%
          float target = clampf(base_ms * mod * 0.001f * samplerate, 10.f, 95990.f);
          fonepole(smooth_time, target, 0.0015f);
          dlyL.SetDelay(smooth_time); dlyR.SetDelay(smooth_time);
          float dl = dlyL.Read(), dr = dlyR.Read();
          float fbAmt = clampf(P3ctrl, 0.f, 0.90f);
          float tone_a = map_lin01(fbAmt, 0.10f, 0.35f); // darker at higher fb
          float fb_inL = dl, fb_inR = dr;
          onepole_lp(fb_inL, fb_inR, tone_a, fb_lpL, fb_lpR);
          dlyL.Write(dryL + fb_lpL * fbAmt);
          dlyR.Write(dryR + fb_lpR * fbAmt);
          wetL = dl; wetR = dr;
        } break;

        case B3_MULTITAP:
        {
          static float baseSamps=24000.f;
          float base_ms = map_exp01(P2ctrl, 60.f, 900.f);
          float target = clampf(base_ms * 0.001f * samplerate, 10.f, 63990.f);
          fonepole(baseSamps, target, 0.0015f);
          // Write once
          dlyL.SetDelay(10.f); dlyR.SetDelay(10.f);
          dlyL.Write(dryL);     dlyR.Write(dryR);
          float taps[3] = { 0.5f*baseSamps, 1.0f*baseSamps, 1.5f*baseSamps };
          float sumL=0.f, sumR=0.f;
          for(int t=0;t<3;t++){
            float d = clampf(taps[t], 10.f, 95990.f);
            dlyL.SetDelay(d); dlyR.SetDelay(d);
            float xL = dlyL.Read(), xR = dlyR.Read();
            float pan = (t - 1) * clampf(P3ctrl, 0.f, 1.f); // spread
            float g   = clampf(1.f - 0.2f*t, 0.5f, 1.f);
            float l = (pan <= 0.f) ? 1.f : (1.f - pan);
            float r = (pan >= 0.f) ? 1.f : (1.f + pan);
            sumL += xL * g * l;
            sumR += xR * g * r;
          }
          wetL = sumL; wetR = sumR;
        } break;

        case B4_ECHOVERB:
        {
          static float smooth_time=24000.f;
          uint32_t now = daisy::System::GetNow();
          bool recent_tap = (now - last_tap_ms) < 2000;
          float target = recent_tap ? clampf(tap_delay_samps, 10.f, 95990.f)
                                    : clampf(map_exp01(P2ctrl, 30.f, 900.f) * 0.001f * samplerate, 10.f, 95990.f);
          fonepole(smooth_time, target, 0.0015f);
          dlyL.SetDelay(smooth_time); dlyR.SetDelay(smooth_time);
          float dl = dlyL.Read(), dr = dlyR.Read();
          float fb01 = clampf(P3ctrl, 0.f, 1.f);
          float fb   = clampf(fb01, 0.f, 0.90f);
          float tone_a = map_lin01(fb01, 0.10f, 0.35f);
          float fbL = dl, fbR = dr; onepole_lp(fbL, fbR, tone_a, fb_lpL, fb_lpR);
          dlyL.Write(dryL + fb_lpL * fb);
          dlyR.Write(dryR + fb_lpR * fb);
          float vL, vR;
          verb.SetFeedback(0.88f);
          verb.SetLpFreq(map_lin01(1.f - fb01, 5000.f, 14000.f));
          verb.Process(dl * map_lin01(fb01, 0.20f, 0.60f),
                       dr * map_lin01(fb01, 0.20f, 0.60f), &vL, &vR);
          wetL = dl + vL; wetR = dr + vR;
        } break;

        case B5_FREEZE:
        {
          // Hold a short window and recycle it with feedback (size via P2, color via P3)
          static float holdSamps = 24000.f;
          float target = clampf(map_exp01(P2ctrl, 40.f, 1200.f)*0.001f*samplerate, 480.f, 64000.f);
          fonepole(holdSamps, target, 0.0015f);
          dlyL.SetDelay(holdSamps); dlyR.SetDelay(holdSamps);
          float dl = dlyL.Read(), dr = dlyR.Read();
          float tone_a = map_lin01(1.f - P3ctrl, 0.08f, 0.35f);
          onepole_lp(dl, dr, tone_a, fb_lpL, fb_lpR);
          // when P2 is very large we fade-in new input less => more "frozen"
          float mixIn = map_lin01(P2ctrl, 0.15f, 0.02f);
          dlyL.Write(dl * 0.98f + dryL * mixIn);
          dlyR.Write(dr * 0.98f + dryR * mixIn);
          wetL = dl; wetR = dr;
        } break;
      }
    }
    else if(bankSel == BANK_C)
    {
      switch(static_cast<PatchC>(patchIdx))
      {
        case C1_CHORUS: {
          float rate = map_exp01(P2ctrl, 0.05f, 3.0f);
          float depth_ms = map_lin01(P3ctrl, 2.0f, 12.0f);
          float base_ms  = 6.0f;
          ch_ph1 += rate / samplerate; if(ch_ph1>=1.f) ch_ph1 -= 1.f;
          ch_ph2 = ch_ph1 + 0.33f; if(ch_ph2>=1.f) ch_ph2 -= 1.f;
          float dL1 = clampf((base_ms + depth_ms * sin01(ch_ph1)) * 0.001f * samplerate, 4.f, 2990.f);
          float dL2 = clampf((base_ms + depth_ms * sin01(ch_ph2)) * 0.001f * samplerate, 4.f, 2990.f);
          float dR1 = clampf((base_ms + depth_ms * sin01(ch_ph1 + 0.5f)) * 0.001f * samplerate, 4.f, 2990.f);
          float dR2 = clampf((base_ms + depth_ms * sin01(ch_ph2 + 0.5f)) * 0.001f * samplerate, 4.f, 2990.f);
          choL1.SetDelay(dL1); choL2.SetDelay(dL2);
          choR1.SetDelay(dR1); choR2.SetDelay(dR2);
          float cL = 0.5f*(choL1.Read() + choL2.Read());
          float cR = 0.5f*(choR1.Read() + choR2.Read());
          choL1.Write(dryL); choL2.Write(dryL);
          choR1.Write(dryR); choR2.Write(dryR);
          wetL = cL; wetR = cR;
        } break;

        case C2_FLANGER: {
          float rate = map_exp01(P2ctrl, 0.05f, 1.5f);
          float min_ms = 0.20f, max_ms = 5.0f;
          flg_ph += rate / samplerate; if(flg_ph>=1.f) flg_ph -= 1.f;
          float d_ms = min_ms + (max_ms - min_ms) * 0.5f * (1.f + sin01(flg_ph));
          float d_samp = clampf(d_ms * 0.001f * samplerate, 4.f, 1990.f);
          flgL.SetDelay(d_samp); flgR.SetDelay(d_samp);
          float dl = flgL.Read(); float dr = flgR.Read();
          float fb = clampf(P3ctrl, 0.f, 0.90f);
          flgL.Write(dryL + dl * fb); flgR.Write(dryR + dr * fb);
          wetL = dl; wetR = dr;
        } break;

        case C3_PHASER: {
          float rate = map_exp01(P2ctrl, 0.05f, 1.5f);
          ph_ph += rate / samplerate; if(ph_ph>=1.f) ph_ph -= 1.f;
          float fc = map_exp01(0.5f*(1.f + sin01(ph_ph)), 300.f, 1800.f);
          float x = expf(-2.f * 3.14159265f * fc / samplerate);
          for(int s=0;s<6;s++){ phL[s].SetCoeff(x); phR[s].SetCoeff(x); }
          float yL = dryL, yR = dryR;
          for(int s=0;s<6;s++){ yL = phL[s].Process(yL); yR = phR[s].Process(yR); }
          float depth = clampf(P3ctrl, 0.f, 0.90f);
          wetL = dryL + depth * (yL - dryL);
          wetR = dryR + depth * (yR - dryR);
        } break;

        case C4_ROTARY: {
          float base = map_exp01(P2ctrl, 0.10f, 6.0f);
          float speed_h = base;
          float speed_d = speed_h * 0.35f;
          rot_ph_h += speed_h / samplerate; if(rot_ph_h>=1.f) rot_ph_h -= 1.f;
          rot_ph_d += speed_d / samplerate; if(rot_ph_d>=1.f) rot_ph_d -= 1.f;
          static float lpfL=0.f,lpfR=0.f,hpfL=0.f,hpfR=0.f;
          float a_lp = 0.10f;
          lpfL += a_lp*(dryL - lpfL); lpfR += a_lp*(dryR - lpfR);
          hpfL = dryL - lpfL;         hpfR = dryR - lpfR;
          float d_amp = 0.5f + 0.5f*sin01(rot_ph_d);
          float h_amp = 0.5f + 0.5f*sin01(rot_ph_h + 0.25f);
          float depth = P3ctrl;
          float d_pan = sin01(rot_ph_d*0.5f)*2.f - 1.f;
          float h_pan = sin01(rot_ph_h*0.5f + 0.25f)*2.f - 1.f;
          auto panL = [](float x, float pan){ float l = sqrtf(0.5f*(1.f - pan)); return x*l; };
          auto panR = [](float x, float pan){ float r = sqrtf(0.5f*(1.f + pan)); return x*r; };
          float dL = panL(lpfL * (0.4f + 0.6f*d_amp*depth), d_pan);
          float dR = panR(lpfR * (0.4f + 0.6f*d_amp*depth), d_pan);
          float hL = panL(hpfL * (0.4f + 0.6f*h_amp*depth), h_pan);
          float hR = panR(hpfR * (0.4f + 0.6f*h_amp*depth), h_pan);
          wetL = dL + hL; wetR = dR + hR;
        } break;

        case C5_VIBRATO: {
          static bool inited=false; 
          if(!inited){ vbL.Init(); vbR.Init(); inited=true; }
          static float ph=0.f;
          float rate = map_exp01(P2ctrl, 0.5f, 8.f);
          float depth_ms = map_lin01(P3ctrl, 0.5f, 6.0f);
          float base_ms  = 3.0f;
          ph += rate / samplerate; if(ph>=1.f) ph -= 1.f;
          float dL = clampf((base_ms + depth_ms * sin01(ph)) * 0.001f * samplerate, 4.f, 1190.f);
          float dR = clampf((base_ms + depth_ms * sin01(ph + 0.5f)) * 0.001f * samplerate, 4.f, 1190.f);
          vbL.SetDelay(dL); vbR.SetDelay(dR);
          float wl = vbL.Read(); float wr = vbR.Read();
          vbL.Write(dryL); vbR.Write(dryR);
          wetL = wl; wetR = wr;
        } break;
      }
    }
    else // BANK_D — Granular family (simple, robust)
    {
      switch(static_cast<PatchD>(patchIdx))
      {
        // ------------- D1 MicroLoop -------------
        case D1_MICROLOOP: {
          // P2: loop size 20..400 ms, P3: feedback color (LP), P1: mix
          float len_ms = map_exp01(P2ctrl, 20.f, 400.f);
          float target = clampf(len_ms*0.001f*samplerate, 960.f, 19200.f);
          fonepole(ml.loop_len_samp, target, 0.0015f);
          // read positions track wr head - loop
          float rp = (float)wr - ml.loop_len_samp; if(rp < 0.f) rp += GRBUF_SAMPS;
          ml.read_posL = rp; ml.read_posR = rp;
          float l = read_wrap(grL, GRBUF_SAMPS, ml.read_posL);
          float r = read_wrap(grR, GRBUF_SAMPS, ml.read_posR);
          // gentle tone control in the loop
          float tone_a = map_lin01(P3ctrl, 0.02f, 0.25f);
          onepole_lp(l, r, tone_a, fb_lpL, fb_lpR);
          wetL = fb_lpL; wetR = fb_lpR;
        } break;

        // ------------- D2 TimeStretch -------------
        case D2_TIMESTRETCH: {
          // P2: rate 0.5..2.0, P3: smear (x-fade)
          ts.rate = map_lin01(P2ctrl, 0.5f, 2.0f);
          float smear = map_lin01(P3ctrl, 0.001f, 0.02f);
          // follow ~300 ms behind write head & move at rate
          if(ts.readL <= 0.f){ ts.readL = (float)wr - 14400.f; if(ts.readL < 0.f) ts.readL += GRBUF_SAMPS; }
          if(ts.readR <= 0.f){ ts.readR = ts.readL; }
          float outL = read_wrap(grL, GRBUF_SAMPS, ts.readL);
          float outR = read_wrap(grR, GRBUF_SAMPS, ts.readR);
          // little smoothing to reduce graininess
          fb_lpL += smear * (outL - fb_lpL);
          fb_lpR += smear * (outR - fb_lpR);
          wetL = fb_lpL; wetR = fb_lpR;
          ts.readL += ts.rate; ts.readR += ts.rate;
          if(ts.readL >= GRBUF_SAMPS) ts.readL -= GRBUF_SAMPS;
          if(ts.readR >= GRBUF_SAMPS) ts.readR -= GRBUF_SAMPS;
        } break;

        // ------------- D3 PitchCloud -------------
        case D3_PITCHCLOUD: {
          // P2: center shift -12..+12 st, P3: spread 0..12 st, mix via P1
          float center = map_lin01(P2ctrl, -12.f, 12.f);
          float spr    = map_lin01(P3ctrl, 0.f, 12.f);
          float s1 = center - spr;
          float s2 = center;
          float s3 = center + spr;
          float mono = 0.5f*(dryL + dryR);
          float a = pc1.Process(mono);
          float b = pc2.Process(mono);
          float c = pc3.Process(mono);
          wetL = 0.6f*a + 0.3f*b + 0.1f*c;
          wetR = 0.1f*a + 0.3f*b + 0.6f*c;
          // update transposition slowly (smooth)
          static float cur1=0.f, cur2=0.f, cur3=0.f;
          fonepole(cur1, s1, 0.001f);
          fonepole(cur2, s2, 0.001f);
          fonepole(cur3, s3, 0.001f);
          pc1.SetTransposition(cur1);
          pc2.SetTransposition(cur2);
          pc3.SetTransposition(cur3);
        } break;

        // ------------- D4 Reverse -------------
        case D4_REVERSE: {
          // P2: window 60..600 ms, P3: crossfade amount
          float win_ms = map_exp01(P2ctrl, 60.f, 600.f);
          float wSamp = clampf(win_ms*0.001f*samplerate, 2880.f, 28800.f);
          revg.win = (uint32_t)wSamp;
          // read goes backwards from write head
          float start = (float)wr - 1.f;
          if(start < 0.f) start += GRBUF_SAMPS;
          float outL = read_wrap(grL, GRBUF_SAMPS, start - (float)(revg.win));
          float outR = read_wrap(grR, GRBUF_SAMPS, start - (float)(revg.win));
          // simple triangular window (fade in/out within window)
          static float env=0.f;
          float xfade = map_lin01(P3ctrl, 0.2f, 1.0f);
          env += (1.f - env) * (1.f / (revg.win * xfade + 1.f));
          float e = env; if(e > 1.f) e = 1.f;
          wetL = outL * e;
          wetR = outR * e;
        } break;

        // ------------- D5 Texture -------------
        case D5_TEXTURE: {
          // P2: grain length 20..120 ms, P3: density 5..50 grains/s
          tex.glen = clampf(map_exp01(P2ctrl, 20.f, 120.f)*0.001f*samplerate, 960.f, 5760.f);
          tex.trig_rate = map_lin01(P3ctrl, 5.f, 50.f);
          // trigger
          tex.ph += tex.trig_rate / samplerate;
          if(tex.ph >= 1.f){
            tex.ph -= 1.f;
            // pick random offset ~10..200 ms behind wr
            float back = map_exp01((float)rand()/RAND_MAX, 10.f, 200.f)*0.001f*samplerate;
            tex.gposL = (float)wr - back; if(tex.gposL < 0.f) tex.gposL += GRBUF_SAMPS;
            tex.gposR = tex.gposL + 200.f; // tiny LR decorrelation
            tex.gph = 0.f;
            tex.pan = (float)rand()/RAND_MAX * 2.f - 1.f;
          }
          // advance grain
          float e = 0.f;
          if(tex.gph <= 1.f){
            float ph = tex.gph;
            e = 0.5f - 0.5f*cosf(2.f*3.14159265f * clampf(ph,0.f,1.f)); // hann
            float gl = read_wrap(grL, GRBUF_SAMPS, tex.gposL);
            float gr = read_wrap(grR, GRBUF_SAMPS, tex.gposR);
            tex.gposL += 1.f; if(tex.gposL >= GRBUF_SAMPS) tex.gposL -= GRBUF_SAMPS;
            tex.gposR += 1.01f; if(tex.gposR >= GRBUF_SAMPS) tex.gposR -= GRBUF_SAMPS;
            tex.gph += 1.f / clampf(tex.glen, 1.f, (float)GRBUF_SAMPS);
            float l = gl * e, r = gr * e;
            // equal-power pan
            float pl = sqrtf(0.5f*(1.f - tex.pan));
            float pr = sqrtf(0.5f*(1.f + tex.pan));
            wetL = l*pl; wetR = r*pr;
          } else {
            wetL = 0.f; wetR = 0.f;
          }
        } break;
      }
    }

    // ------ Final mix + output filtering (applies to all FX) ------
    float mixOutL = (1.f - mixAmt)*dryL + mixAmt*wetL;
    float mixOutR = (1.f - mixAmt)*dryR + mixAmt*wetR;

    mixOutL = dcL.Process(mixOutL);
    mixOutR = dcR.Process(mixOutR);
    mixOutL = oplpL.Process(mixOutL);
    mixOutR = oplpR.Process(mixOutR);

    out[0][i] = mixOutL;
    out[1][i] = mixOutR;
  }
}

// ================== OLED (helpers in a namespace to avoid auto-prototype issues) ==================
namespace ui {

// 6 px per char at textSize=1. Clip to fit inside width w with ~10px padding.
static void printClipped(int x, int y, int w, const char* s)
{
  int maxChars = (w - 10) / 6;
  if(maxChars <= 0){ return; }
  int n=0; while(s[n] && n < maxChars) n++;
  char buf[32];
  if(n >= (int)sizeof(buf)) n = sizeof(buf)-1;
  memcpy(buf, s, n); buf[n] = 0;
  oled.setCursor(x, y);
  oled.print(buf);
}

// Faux-bold (double print 1px offset) keeping same text size
static void printSameSize(int x, int y, const char* s, bool bold)
{
  oled.setCursor(x, y);
  oled.print(s);
  if(bold){
    oled.setCursor(x+1, y);
    oled.print(s);
  }
}

static void printClippedBold(int x, int y, int w, const char* s, bool bold)
{
  int maxChars = (w - 10) / 6;
  if(maxChars <= 0){ return; }
  int n=0; while(s[n] && n < maxChars) n++;
  char buf[32];
  if(n >= (int)sizeof(buf)) n = sizeof(buf)-1;
  memcpy(buf, s, n); buf[n] = 0;
  oled.setCursor(x, y); oled.print(buf);
  if(bold){ oled.setCursor(x+1, y); oled.print(buf); }
}

static void drawBar(int x, int y, int w, int h, float amt, bool invert=false){
  amt = clampf(amt, 0.f, 1.f);
  int fill = (int)((w-2)*amt + 0.5f);
  if(invert) oled.fillRect(x, y, w, h, SSD1306_WHITE);
  oled.drawRect(x, y, w, h, SSD1306_WHITE);
  if(fill>0) oled.fillRect(x+1, y+1, fill, h-2, invert ? SSD1306_BLACK : SSD1306_WHITE);
}

static const char* GetBankTitle(Bank b){
  switch(b){
    case BANK_A: return "Reverb";
    case BANK_B: return "Delay";
    case BANK_C: return "Mod";
    case BANK_D: return "Granular";
  }
  return "(?)";
}

static const char* patchTitleShort(){
  if(bankSel==BANK_A){
    switch(static_cast<PatchA>(patchIdx)){
      case A1_CLASSIC: return "A1 Classic";
      case A2_PLATE:   return "A2 Plate";
      case A3_TANK:    return "A3 Tank";
      case A4_SHIMMER: return "A4 Shimmer";
      case A5_GHOST:   return "A5 Ghost";
    }
  }else if(bankSel==BANK_B){
    switch(static_cast<PatchB>(patchIdx)){
      case B1_PING:     return "B1 Ping";
      case B2_TAPE:     return "B2 Tape";
      case B3_MULTITAP: return "B3 MultiTap";
      case B4_ECHOVERB: return "B4 Echo";
      case B5_FREEZE:   return "B5 Freeze";
    }
  }else if(bankSel==BANK_C){
    switch(static_cast<PatchC>(patchIdx)){
      case C1_CHORUS:   return "C1 Chorus";
      case C2_FLANGER:  return "C2 Flanger";
      case C3_PHASER:   return "C3 Phaser";
      case C4_ROTARY:   return "C4 Rotary";
      case C5_VIBRATO:  return "C5 Vibrato";
    }
  }else{
    switch(static_cast<PatchD>(patchIdx)){
      case D1_MICROLOOP:   return "D1 MicroLoop";
      case D2_TIMESTRETCH: return "D2 TimeStretch";
      case D3_PITCHCLOUD:  return "D3 PitchCloud";
      case D4_REVERSE:     return "D4 Reverse";
      case D5_TEXTURE:     return "D5 Texture";
    }
  }
  return "";
}

static void drawBankMenu(Bank highlight)
{
  oled.clearDisplay();
  oled.setTextSize(1);
  oled.setTextColor(SSD1306_WHITE);

  // Status bar
  oled.fillRect(0, 0, OLED_W, 12, SSD1306_WHITE);
  oled.setTextColor(SSD1306_BLACK);
  ui::printClipped(2, 2, OLED_W-4, "Bank (short: next  long: enter)");
  oled.setTextColor(SSD1306_WHITE);

  int cellW = OLED_W/2, cellH = (OLED_H-12)/2;
  int xL=0, xR=cellW;
  int y1=12, y2=12+cellH;

  auto cell=[&](int x,int y,const char* label,bool hilite){
    oled.drawRect(x,y,cellW,cellH,SSD1306_WHITE);
    int textX = x + 6;
    int textY = y + cellH/2 - 4;
    ui::printClippedBold(textX, textY, cellW-12, label, hilite /*bold*/);
  };

  cell(xL,y1,GetBankTitle(BANK_A),highlight==BANK_A);
  cell(xR,y1,GetBankTitle(BANK_B),highlight==BANK_B);
  cell(xL,y2,GetBankTitle(BANK_C),highlight==BANK_C);
  cell(xR,y2,GetBankTitle(BANK_D),highlight==BANK_D);

  oled.display();
}

static void drawPatchUi(bool btn_pressed, bool showTapFlag)
{
  oled.clearDisplay();
  oled.setTextSize(1);

  oled.fillRect(0, 0, OLED_W, 12, SSD1306_WHITE);
  oled.setTextColor(SSD1306_BLACK);
  ui::printClipped(2, 2, 96, patchTitleShort());
  if(showTapFlag) ui::printClipped(100, 2, 26, "[TAP]");
  oled.setTextColor(SSD1306_WHITE);

  const int yRow1 = 14, yRow2 = 38;
  const int cellW_L = 60, cellW_R = 68, cellH = 22;

  oled.drawRect(0, yRow1, cellW_L, cellH, SSD1306_WHITE);
  ui::printClipped(4, yRow1+2, cellW_L-8, "Btn: P-> / Bank");
  ui::drawBar(4, yRow1 + cellH - 9, cellW_L - 8, 7, btn_pressed ? 1.f : 0.f);

  oled.drawRect(cellW_L, yRow1, cellW_R, cellH, SSD1306_WHITE);
  {
    char line[24];
    int mixPct = (int)roundf(P1*100.f);
    snprintf(line, sizeof(line), "P1 Mix %d%%", mixPct);
    ui::printClipped(cellW_L+4, yRow1+2, cellW_R-8, line);
  }
  ui::drawBar(cellW_L+4, yRow1 + cellH - 9, cellW_R - 8, 7, P1);

  oled.drawRect(0, yRow2, cellW_L, cellH, SSD1306_WHITE);
  {
    const char* p2name =
      (bankSel==BANK_A) ? ((patchIdx==A2_PLATE || patchIdx==A3_TANK) ? "P2 Pre" : "P2 Decay") :
      (bankSel==BANK_B) ? "P2 Time" :
      (bankSel==BANK_C) ? "P2 Rate" : "P2 Size/Rate";
    char line[24];
    int p2pct = (int)roundf((toP2.cv_mode ? cv_uni01(CV1_volts) : P2)*100.f);
    snprintf(line, sizeof(line), "%s %d%%", p2name, p2pct);
    ui::printClipped(4, yRow2+2, cellW_L-8, line);
  }
  ui::drawBar(4, yRow2 + cellH - 9, cellW_L - 8, 7, (toP2.cv_mode ? cv_uni01(CV1_volts) : P2), toP2.cv_mode);

  oled.drawRect(cellW_L, yRow2, cellW_R, cellH, SSD1306_WHITE);
  {
    const char* p3name;
    if(bankSel==BANK_A) p3name = (patchIdx==A4_SHIMMER) ? "P3 Shim" : "P3 Tone";
    else if(bankSel==BANK_B) p3name = (patchIdx==B4_ECHOVERB) ? "P3 Macro" : "P3 FBk";
    else if(bankSel==BANK_C) p3name = "P3 Depth";
    else p3name = "P3 Grain/Tone";
    char line[24];
    int p3pct = (int)roundf((toP3.cv_mode ? cv_uni01(CV2_volts) : P3)*100.f);
    snprintf(line, sizeof(line), "%s %d%%", p3name, p3pct);
    ui::printClipped(cellW_L+4, yRow2+2, cellW_R-8, line);
  }
  ui::drawBar(cellW_L+4, yRow2 + cellH - 9, cellW_R - 8, 7, (toP3.cv_mode ? cv_uni01(CV2_volts) : P3), toP3.cv_mode);

  oled.display();
}

} // namespace ui

// ================== SETUP / LOOP ==================
void setup()
{
  Serial.begin(115200);
  uint32_t t0 = millis();
  while(!Serial && (millis()-t0)<1500) {}
  Serial.println("DaisyMFX: setup starting...");

  hw = DAISY.init(DAISY_PATCH, AUDIO_SR_48K);
  samplerate = DAISY.get_samplerate();
  analogReadResolution(16);

  // I2C1
  Wire.setSCL(PIN_SCL);
  Wire.setSDA(PIN_SDA);
  Wire.begin();
  Wire.setClock(I2C_CLOCK_HZ);   // slow the I²C edges a bit

  pinMode(PIN_BTN, INPUT_PULLUP);
  pinMode(PIN_LED, OUTPUT);

  if(!oled.begin(SSD1306_SWITCHCAPVCC, OLED_ADDR)){
    Serial.println("OLED init failed — blinking LED.");
    for(;;){ digitalWrite(PIN_LED, !digitalRead(PIN_LED)); delay(150); }
  }

  // Lower brightness / contrast immediately
  oled.dim(true);                              // reduce segment current
  oled.ssd1306_command(SSD1306_SETCONTRAST);   // 0x81
  oled.ssd1306_command(UI_LOW_CONTRAST);       // very low contrast

  // DSP init
  verb.Init(samplerate);
  preL_A1.Init(); preR_A1.Init();
  preL_A2.Init(); preR_A2.Init();
  preL_A3.Init(); preR_A3.Init();
  modL_A3.Init(); modR_A3.Init();
  shifter.Init(samplerate); shifter.SetTransposition(12.f);
  dlyL.Init(); dlyR.Init();
  choL1.Init(); choL2.Init(); choR1.Init(); choR2.Init();
  flgL.Init(); flgR.Init();
  a3mL.Init(); a3mR.Init();
  ghoML.Init(); ghoMR.Init();
  vbL.Init(); vbR.Init();

  pc1.Init(samplerate); pc2.Init(samplerate); pc3.Init(samplerate);
  pc1.SetTransposition(0.f); pc2.SetTransposition(0.f); pc3.SetTransposition(0.f);

  // Output LP around 16 kHz to shave hiss
  oplpL.SetCutoff(16000.f, samplerate);
  oplpR.SetCutoff(16000.f, samplerate);

  // Clear OLED and draw first screen
  ui::drawBankMenu(previewBank);
  g_last_user_ms = millis(); // start awake

  Serial.println("DaisyMFX: audio starting");
  DAISY.begin(AudioCallback);
  Serial.println("DaisyMFX: ready");
}

void loop()
{
  // Heartbeat
  digitalWrite(PIN_LED, (millis()/500)%2);

  // Pots (smoothed, CW=max)
  P1 = 0.98f*P1 + 0.02f*readPotInv01(PIN_POT1);
  P2 = 0.98f*P2 + 0.02f*readPotInv01(PIN_POT2);
  P3 = 0.98f*P3 + 0.02f*readPotInv01(PIN_POT3);

  // CV (smoothed) + raw for tap edge
  float cv1_a01 = analogRead(PIN_CV1)/65535.f;
  float cv2_a01 = analogRead(PIN_CV2)/65535.f;
  float cv1_v = Adc01ToVin(cv1_a01);
  float cv2_v = Adc01ToVin(cv2_a01);
  CV1_volts = 0.95f*CV1_volts + 0.05f*cv1_v;
  CV2_volts = 0.90f*CV2_volts + 0.10f*cv2_v;
  CV2_volts_raw = cv2_v;

  // CV2 edge tap (Delays only)
  if(bankSel==BANK_B){
    uint32_t now = daisy::System::GetNow();
    if(!tap_gate && CV2_volts_raw >= TAP_HIGH){
      tap_gate = true;
      uint32_t dt = now - last_tap_ms;
      if(dt > 50 && dt < 2000){
        tap_delay_samps = (dt / 1000.f) * samplerate;
      }
      last_tap_ms = now;
    } else if(tap_gate && CV2_volts_raw <= TAP_LOW){
      tap_gate = false;
    }
  }

  // Button navigation
  bool pressed = (digitalRead(PIN_BTN) == LOW);
  uint32_t now = daisy::System::GetNow();
  if(pressed && !btn_prev) btn_down_ms = now;
  if(!pressed && btn_prev){
    uint32_t held = now - btn_down_ms;
    if(held >= 800){
      // Long press: switch level (Patch <-> Bank)
      if(level == LEVEL_BANK){
        bankSel = previewBank;
        patchIdx = 0;
        verb.Init(samplerate);
        dlyL.Reset(); dlyR.Reset();
        level = LEVEL_PATCH;
        Serial.printf("Enter bank=%d\n", (int)bankSel);
      } else {
        previewBank = bankSel;
        level = LEVEL_BANK;
      }
    } else {
      // Short press: cycle within current level
      if(level == LEVEL_BANK){
        previewBank = (Bank)((((int)previewBank)+1) % 4);
      } else {
        patchIdx = (patchIdx + 1) % PatchesInBank(bankSel);
        Serial.printf("Patch=%d\n", patchIdx);
      }
    }
  }
  btn_prev = pressed;

  // ---------- Event-driven UI with sleep & throttling ----------
  static uint32_t last_draw = 0;
  static float p1_last=-1.f, p2_last=-1.f, p3_last=-1.f;
  static int   patch_last=-1;
  static Bank  bank_last=(Bank)255;
  bool showTap = (bankSel==BANK_B) && ((now - last_tap_ms) < 200);

  // Detect "user interaction" for wake/sleep purposes
  bool user_interaction =
      pressed ||
      fabsf(P1 - p1_last) > UI_CHANGE_EPS ||
      fabsf(P2 - p2_last) > UI_CHANGE_EPS ||
      fabsf(P3 - p3_last) > UI_CHANGE_EPS ||
      (patchIdx != patch_last) ||
      (bankSel  != bank_last) ||
      showTap;

  // Update last-interaction timestamp and wake if needed
  if(user_interaction){
    g_last_user_ms = millis();
    OledWake();
  }

  // Auto-sleep if idle
  if(millis() - g_last_user_ms > UI_IDLE_SLEEP_MS){
    OledSleep();
  }

  // Only draw if awake, throttled, and something changed
  bool throttle_ok = (millis() - last_draw) >= UI_FRAME_MIN_MS;
  bool values_changed = user_interaction;

  if(g_oled_awake && throttle_ok && values_changed){
    last_draw = millis();
    p1_last = P1; p2_last = P2; p3_last = P3;
    patch_last = patchIdx; bank_last = bankSel;

    if(level == LEVEL_BANK) ui::drawBankMenu(previewBank);
    else                    ui::drawPatchUi(pressed, showTap);
  }
}

