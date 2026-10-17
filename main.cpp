// BodyTex.asi v0.4 - GTA San Andreas (1.0 US) - plugin-sdk
// Menu: black / gold / RGB theme, "texture menu create by : Parsa Rsi" header (Watch Dogs 2 glitch name)
// Category 1: apply any in-game texture to car BODY materials only
// Category 2: code-only animated paint jobs (no images)
// Typing PRS opens the mouse menu (camera frozen, free cursor, RGB-border UI).
// Shortcuts with menu closed: Num6/Num4 next/prev | Num9/Num3 +-100 (cat 1) | Num0 off
// F9 = invert mouse | F10 = glow light on/off. The paint stays on the car after you get out.
#include "plugin.h"
#include "common.h"
#include "CTxdStore.h"
#include "TxdDef.h"
#include "NodeName.h"
#include "CStreaming.h"
#include "CPools.h"
#include "CVehicle.h"
#include "CModelInfo.h"
#include "CTimer.h"
#include "CFont.h"
#include "CPointLights.h"
#include "CSprite2d.h"
#include "CPad.h"
#include "CRect.h"
#include "CRGBA.h"
#include <vector>
#include <string>
#include <cmath>
#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <cstdint>

using namespace plugin;

// ---------------- config ----------------
static const int   DYN_SIZE  = 256;   // size of generated texture
static const int   DYN_EVERY = 3;     // update texture every N frames
static const char* LOG_FILE  = "BodyTex.log";

// ---------------- log ----------------
static void Log(const char* fmt, ...) {
    FILE* f = fopen(LOG_FILE, "a");
    if (!f) return;
    va_list a; va_start(a, fmt);
    vfprintf(f, fmt, a);
    va_end(a);
    fputc('\n', f);
    fclose(f);
}

// ---------------- state ----------------
struct MatRec {
    RpMaterial* mat;
    RwTexture* origTex;
    RwSurfaceProperties origProps;
    char frame[40];   // part (frame) name this material belongs to
    char tex[32];     // original texture name
    char why[16];     // reason it is skipped by default
    bool on;          // currently painted by the mod
    bool autoOn;      // automatic decision
    bool canUse;      // geometry has UVs, so it can be painted
};
static std::vector<MatRec> g_recs;
static int g_partPage = 0;   // page of the parts list in the menu
static CVehicle* g_veh = nullptr;
static int g_vehModel = -1;
static unsigned char g_origCols[4] = {0, 0, 0, 0};
static int g_mode = 0;  // 0 off, 1 category 1, 2 category 2

// ---------------- string helpers ----------------
static bool Has(const char* s, const char* sub) {
    if (!s || !sub) return false;
    std::string a(s), b(sub);
    for (auto& c : a) c = (char)tolower((unsigned char)c);
    for (auto& c : b) c = (char)tolower((unsigned char)c);
    return a.find(b) != std::string::npos;
}
static bool HasAny(const char* s, const char* const* list) {
    for (int i = 0; list[i]; i++) if (Has(s, list[i])) return true;
    return false;
}
static const char* const FRAME_EXCL[] = {"wheel", "tyre", "tire", "windscreen", "window", "glass", "exhaust",
    "light", "lamp", "plate", "interior", "steer", "shadow", "wiper", nullptr};
static const char* const FRAME_BODY[] = {"chassis", "bonnet", "boot", "door", "bump", "wing", "misc", "roof",
    "spoiler", "body", "hood", "fender", "panel", "skirt", "extra", nullptr};
static const char* const TEX_EXCL[] = {"glass", "window", "tire", "tyre", "wheel", "plate", "interior", "dash",
    "seat", "light", "lamp", "chrome", "exhaust", "grill", nullptr};

// ---------------- body analysis ----------------
static bool IsMarker(const RwRGBA* c) {
    return (c->red == 60 && c->green == 255 && c->blue == 0) ||
           (c->red == 255 && c->green == 0 && c->blue == 175) ||
           (c->red == 0 && c->green == 255 && c->blue == 255) ||
           (c->red == 255 && c->green == 0 && c->blue == 255);
}
struct WalkCtx {
    const char* frame;
    bool hasUV;
    bool frameExcl;
    bool frameBody;
};
static RpMaterial* MatCB(RpMaterial* m, void* d) {
    WalkCtx* c = (WalkCtx*)d;
    if (!m) return m;
    for (auto& e : g_recs) if (e.mat == m) return m;  // shared between atomics
    const RwRGBA* col = RpMaterialGetColor(m);
    RwTexture* t = RpMaterialGetTexture(m);
    const char* tn = t ? t->name : "";
    bool marker = col && IsMarker(col);
    // every material of every part is recorded; it gets the paint unless it is clearly not bodywork
    const char* why = "";
    if (!col || col->alpha < 255) why = "glass";
    else if (c->frameExcl) why = "frame";
    else if (t && !marker && HasAny(tn, TEX_EXCL)) why = "tex";
    else if (!c->hasUV) why = "noUV";
    MatRec r = {};
    r.mat = m;
    r.origTex = t;
    const RwSurfaceProperties* sp = RpMaterialGetSurfaceProperties(m);
    if (sp) r.origProps = *sp; else { r.origProps.ambient = 1.0f; r.origProps.specular = 0.0f; r.origProps.diffuse = 1.0f; }
    if (t) t->refCount++;  // keep original alive
    strncpy(r.frame, c->frame, sizeof(r.frame) - 1);
    strncpy(r.tex, tn, sizeof(r.tex) - 1);
    strncpy(r.why, why, sizeof(r.why) - 1);
    r.autoOn = (why[0] == 0);
    r.on = r.autoOn;
    r.canUse = c->hasUV;
    Log("  part frame=%s tex=%s marker=%d -> %s %s", c->frame, tn, marker ? 1 : 0, r.on ? "ON" : "off", why);
    g_recs.push_back(r);
    return m;
}
static RpAtomic* AtomCB(RpAtomic* a, void*) {
    if (!a) return a;
    RpGeometry* g = RpAtomicGetGeometry(a);
    RwFrame* f = RpAtomicGetFrame(a);
    if (!g || !f) return a;
    const char* fn = GetFrameNodeName(f);
    if (!fn) fn = "";
    WalkCtx ctx;
    ctx.frame = fn;
    ctx.hasUV = RpGeometryGetNumTexCoordSets(g) > 0;
    ctx.frameExcl = HasAny(fn, FRAME_EXCL);
    ctx.frameBody = HasAny(fn, FRAME_BODY);
    Log(" frame '%s' excl=%d body=%d uv=%d", fn, ctx.frameExcl, ctx.frameBody, ctx.hasUV);
    RpGeometryForAllMaterials(g, MatCB, &ctx);
    return a;
}

static bool VehicleAlive(CVehicle* v) {
    if (!v) return false;
    auto pool = CPools::ms_pVehiclePool;
    if (!pool) return false;
    for (int i = 0; i < pool->m_nSize; i++)
        if (!pool->IsFreeSlotAtIndex(i) && pool->GetAt(i) == v) return true;
    return false;
}

// ---------------- category 1: texture catalog ----------------
static int g_nSlots = 0, g_slot = -1, g_idx = 0;
static bool g_opened = false, g_weLoaded = false;
static std::vector<RwTexture*> g_tex;

static RwTexDictionary* TxdGet(int slot) {
    auto pool = CTxdStore::ms_pTxdPool;
    if (!pool || slot < 0 || slot >= pool->m_nSize || pool->IsFreeSlotAtIndex(slot)) return nullptr;
    TxdDef* d = pool->GetAt(slot);
    return d ? d->m_pRwDictionary : nullptr;
}
static bool SlotValid(int s) {
    return s >= 0 && s < g_nSlots && !CTxdStore::ms_pTxdPool->IsFreeSlotAtIndex(s);
}
static bool LoadTxd(int slot) {
    __try {
        if (TxdGet(slot)) return true;
        CStreaming::RequestModel(20000 + slot, 2);
        CStreaming::LoadAllRequestedModels(false);
        return TxdGet(slot) != nullptr;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return false;
    }
}
static RwTexture* TexCB(RwTexture* t, void* d) {
    ((std::vector<RwTexture*>*)d)->push_back(t);
    return t;
}
static void CloseSlot() {
    if (g_opened && g_slot >= 0) {
        CTxdStore::RemoveRef(g_slot);
        if (g_weLoaded) CStreaming::SetModelIsDeletable(20000 + g_slot);
    }
    g_tex.clear();
    g_opened = false;
}
static void OpenSlot(int s) {
    CloseSlot();
    g_slot = s;
    bool was = TxdGet(s) != nullptr;
    if (!LoadTxd(s)) return;
    RwTexDictionary* dict = TxdGet(s);
    if (!dict) return;
    CTxdStore::AddRef(s);
    g_opened = true;
    g_weLoaded = !was;
    RwTexDictionaryForAllTextures(dict, TexCB, &g_tex);
}
static int FirstValid() { for (int i = 0; i < g_nSlots; i++) if (SlotValid(i)) return i; return -1; }
static int LastValid() { for (int i = g_nSlots - 1; i >= 0; i--) if (SlotValid(i)) return i; return -1; }

static int g_navPending = 0;   // queued prev/next steps (sign = direction), worked off a little per frame
static int g_opensFrame = 0;   // TXD loads done this frame
static const int MAX_OPENS_PER_FRAME = 2;

// returns 1 = moved, 0 = nothing to show, 2 = out of per-frame budget (try again next frame)
static int Step(int dir) {
    if (!CTxdStore::ms_pTxdPool) return 0;
    g_nSlots = CTxdStore::ms_pTxdPool->m_nSize;
    int guard = 0;
    while (guard <= g_nSlots + 2) {
        int ni = g_idx + dir;
        if (g_slot >= 0 && g_opened && ni >= 0 && ni < (int)g_tex.size()) { g_idx = ni; return 1; }
        if (g_opensFrame >= MAX_OPENS_PER_FRAME) return 2;
        int s = g_slot < 0 ? (dir > 0 ? -1 : g_nSlots) : g_slot;
        do { s += dir; } while (s >= 0 && s < g_nSlots && !SlotValid(s));
        if (s < 0 || s >= g_nSlots) s = dir > 0 ? FirstValid() : LastValid();
        if (s < 0) return 0;
        OpenSlot(s);
        g_opensFrame++;
        guard++;
        g_idx = dir > 0 ? -1 : (int)g_tex.size();
    }
    return 0;
}
static RwTexture* CurTex() {
    if (g_opened && g_idx >= 0 && g_idx < (int)g_tex.size()) return g_tex[g_idx];
    return nullptr;
}

// ---------------- category 2: procedural paint ----------------
static RwRaster* g_dynRaster = nullptr;
static RwTexture* g_dynTex = nullptr;
static int g_design = 0;
static int g_frame = 0;
static const int N_DESIGNS = 36;
static const char* DESIGN_NAME[N_DESIGNS] = {"Rainbow wave", "Fire", "Plasma", "Matrix", "Shapes & symbols",
    "Neon lines (glow)", "Lightning (glow)", "Pulse rings (glow)", "Energy streaks (glow)",
    "Aurora", "Neon grid", "Gold shimmer", "Cyber stripes", "Starfield", "Lava", "Ice crystals", "Equalizer",
    "Radar sweep", "Hyperspace", "Police lights", "Rainbow spiral", "Ripples", "Synthwave", "Neon bokeh",
    "Liquid chrome", "Acid plasma", "Nebula", "Gold & black", "Circuit pulses", "Electric waves", "Fire & Ice",
    "Disco tiles", "Laser beams", "Caustics", "Hearts pulse", "Golden stars"};
static const int FIRST_GLOW = 5;

static float Hh(int a, int b = 0, int c = 0) {
    unsigned x = (unsigned)a * 374761393u + (unsigned)b * 668265263u + (unsigned)c * 2147483647u;
    x = (x ^ (x >> 13)) * 1274126177u;
    x ^= x >> 16;
    return (x & 0xFFFF) / 65535.0f;
}
static inline float Cl(float v) { return v < 0 ? 0 : (v > 1 ? 1 : v); }
static inline float Fr(float x) { return x - floorf(x); }
static inline uint32_t Pack(float r, float g, float b) {
    return 0xFF000000u | ((uint32_t)(Cl(r) * 255) << 16) | ((uint32_t)(Cl(g) * 255) << 8) | (uint32_t)(Cl(b) * 255);
}
static void Hsv(float h, float s, float v, float& r, float& g, float& b) {
    h = h - floorf(h);
    float k = h * 6.0f; int i = (int)k; float f = k - i;
    float p = v * (1 - s), q = v * (1 - s * f), t = v * (1 - s * (1 - f));
    switch (i % 6) {
        case 0: r = v; g = t; b = p; break;
        case 1: r = q; g = v; b = p; break;
        case 2: r = p; g = v; b = t; break;
        case 3: r = p; g = q; b = v; break;
        case 4: r = t; g = p; b = v; break;
        default: r = v; g = p; b = q; break;
    }
}
// shape coverage in x,y in [-1,1], y down
static bool Shape(int id, float x, float y) {
    switch (id) {
        case 0: { float X = x * 1.3f, Y = -y * 1.2f + 0.2f; float a = X * X + Y * Y - 1; return a * a * a - X * X * Y * Y * Y < 0; }
        case 1: { float r = sqrtf(x * x + y * y), th = atan2f(y, x); return r < 0.55f + 0.4f * cosf(5 * (th + 1.5708f)); }
        case 2: {
            float r = sqrtf(x * x + y * y);
            bool eyes = (powf(fabsf(x) - 0.3f, 2) + powf(y + 0.25f, 2)) < 0.0144f;
            bool mouth = r > 0.45f && r < 0.57f && y > 0.15f;
            return r < 0.9f && !eyes && !mouth;
        }
        case 3: {
            float r = sqrtf(x * x + y * y);
            bool ring = r > 0.75f && r < 0.9f;
            bool vl = fabsf(x) < 0.07f && fabsf(y) < 0.9f;
            bool dr = y > 0 && x > 0 && fabsf(x - y) < 0.1f && r < 0.9f;
            bool dl = y > 0 && x < 0 && fabsf(x + y) < 0.1f && r < 0.9f;
            return ring || vl || dr || dl;
        }
        default: {
            bool head = (x * x + (y + 0.15f) * (y + 0.15f)) < 0.42f;
            bool jaw = fabsf(x) < 0.35f && y > 0.2f && y < 0.75f;
            bool eyes = (powf(fabsf(x) - 0.27f, 2) + powf(y + 0.15f, 2)) < 0.04f;
            bool nose = (x * x + (y - 0.12f) * (y - 0.12f)) < 0.0064f;
            return (head || jaw) && !eyes && !nose;
        }
    }
}
static uint32_t Pixel(int design, float u, float v, float t) {
    float r = 0, g = 0, b = 0;
    const float kPi = 3.14159265f;
    switch (design) {
        case 0: Hsv(u + v * 0.5f + t * 0.3f + 0.15f * sinf(v * 12 + t * 2), 1, 1, r, g, b); break;
        case 1: {
            float fl = Cl((1 - v) * 1.4f + 0.35f * sinf(u * 18 + t * 6) * sinf(v * 9 - t * 5));
            r = fminf(1, fl * 2); g = Cl(fl * 2 - 0.7f); b = Cl(fl * 3 - 2.4f); break;
        }
        case 2: {
            float val = sinf(u * 10 + t) + sinf(v * 8 - t * 1.3f) + sinf((u + v) * 6 + t * 0.7f) + sinf(sqrtf(u * u + v * v) * 12 - t);
            r = 0.5f + 0.5f * sinf(val * kPi * 0.5f); g = 0.5f + 0.5f * sinf(val * kPi * 0.5f + 2); b = 0.5f + 0.5f * sinf(val * kPi * 0.5f + 4); break;
        }
        case 3: {
            int col = (int)(u * 24), row = (int)(v * 24);
            float sp = 0.3f + Hh(col) * 0.7f;
            float head = fmodf(t * sp + Hh(col, 7), 1.0f);
            float d = fmodf(head - v + 1.0f, 1.0f);
            float br = d < 0.35f ? 1 - d / 0.35f : 0;
            float mask = Hh(col, row, (int)(t * 8)) > 0.4f ? 1.0f : 0.5f;
            br *= mask;
            r = d < 0.03f ? br : 0; g = br; b = br * 0.25f; break;
        }
        case 4: {
            float su = u * 4 + t * 0.25f, sv = v * 4;
            int id = (int)(Hh((int)floorf(su), (int)floorf(sv)) * 5) % 5;
            float x = (su - floorf(su)) * 2 - 1, y = (sv - floorf(sv)) * 2 - 1;
            if (Shape(id, x, y)) Hsv(t * 0.2f + id * 0.2f, 0.9f, 1, r, g, b);
            else { Hsv(t * 0.1f + v * 0.3f, 0.8f, 0.25f, r, g, b); }
            break;
        }
        case 5: {
            float d1 = fabsf(fmodf(u * 3 + v * 3 + t * 0.5f, 1.0f) - 0.5f);
            float d2 = fabsf(fmodf(u * 2 - v * 2 - t * 0.4f + 10.0f, 1.0f) - 0.5f);
            float in = (expf(-d1 * d1 * 400) + expf(-d2 * d2 * 400)) * (0.6f + 0.4f * sinf(t * 6));
            Hsv(t * 0.2f + u, 1, 1, r, g, b); r *= in; g *= in; b *= in; break;
        }
        case 6: {
            float in = 0;
            for (int i = 0; i < 3; i++) {
                float cx = 0.2f + 0.3f * i + 0.06f * sinf(v * 30 + Hh((int)(t * 6), i) * 10) + 0.04f * sinf(v * 80 + i);
                float d = fabsf(u - cx);
                bool on = Hh((int)(t * 10), i, 3) > 0.55f;
                if (on) in += expf(-d * d * 5000) + 0.25f * expf(-d * d * 300);
            }
            float bg = 0.05f + 0.05f * sinf(t * 3);
            r = Cl(in * 0.8f + bg * 0.3f); g = Cl(in * 0.9f + bg * 0.3f); b = Cl(in + bg); break;
        }
        case 7: {
            float x = fmodf(u * 2, 1.0f) - 0.5f, y = fmodf(v * 2, 1.0f) - 0.5f;
            float rr = sqrtf(x * x + y * y);
            float q = fmodf(rr * 4 - t * 1.2f + 10.0f, 1.0f) - 0.5f;
            float in = expf(-q * q * 200);
            Hsv(0.5f + rr * 0.8f + t * 0.1f, 1, 1, r, g, b); r *= in; g *= in; b *= in; break;
        }
        case 9: {  // Aurora
            float w1 = 0.5f + 0.5f * sinf(u * 5 + t * 0.8f + sinf(v * 3 + t * 0.5f) * 1.5f);
            float w2 = 0.5f + 0.5f * sinf(u * 8 - t * 0.6f + sinf(v * 5 - t * 0.4f) * 2.0f);
            float br = Cl(0.15f + w1 * w1 * 0.8f * (0.5f + 0.5f * (1 - v)) + w2 * w2 * 0.3f);
            Hsv(0.42f + 0.28f * w2, 0.75f, br, r, g, b); break;
        }
        case 10: {  // Neon grid
            float gu = fabsf(Fr(u * 8 + t * 0.25f) - 0.5f), gv = fabsf(Fr(v * 8 - t * 0.2f) - 0.5f);
            float dd = fminf(gu, gv);
            float in = expf(-dd * dd * 900.0f) * (0.7f + 0.3f * sinf(t * 4 + u * 10)) + 0.03f;
            Hsv(0.5f + u * 0.4f + t * 0.08f, 1, 1, r, g, b); r *= in; g *= in; b *= in; break;
        }
        case 11: {  // Gold shimmer
            float s = 0.5f + 0.5f * sinf(u * 6 + v * 4 + t * 1.2f + sinf(v * 9 - t) * 1.5f);
            float br = 0.25f + 0.75f * s * s;
            r = br; g = br * 0.78f; b = br * 0.22f;
            if (Hh((int)(u * 48), (int)(v * 48), (int)(t * 5)) > 0.985f) { r = g = b = 1.0f; }
            break;
        }
        case 12: {  // Cyber stripes
            float m = 0.5f + 0.5f * sinf((u + v) * 18.0f - t * 3.0f);
            Hsv(0.5f + 0.33f * m, 1, 0.15f + 0.85f * m * m, r, g, b); break;
        }
        case 13: {  // Starfield
            const float N = 40.0f;
            int cx = (int)(u * N), cy = (int)(v * N);
            float h = Hh(cx, cy, 1);
            float fu = u * N - cx - 0.5f, fv = v * N - cy - 0.5f;
            float tw = 0.5f + 0.5f * sinf(t * (2 + h * 5) + h * 30);
            float in = (h > 0.82f) ? tw * expf(-(fu * fu + fv * fv) * 25.0f) : 0.0f;
            float bg = 0.06f + 0.06f * v, hh = Hh(cx, cy, 5);
            r = bg * 0.4f + in * (0.7f + 0.3f * hh); g = bg * 0.5f + in * 0.85f; b = bg + in * (1.0f - 0.3f * hh); break;
        }
        case 14: {  // Lava
            float cx = u - 0.5f, cy = v - 0.5f;
            float val = sinf(u * 6 + t * 0.6f) + sinf(v * 7 - t * 0.8f) + sinf((u + v) * 5 + t * 0.5f) + sinf(sqrtf(cx * cx + cy * cy) * 14 - t);
            float fl = Cl(0.5f + 0.25f * val); fl *= fl;
            r = Cl(fl * 2.2f); g = Cl(fl * 1.4f - 0.25f); b = Cl(fl * 0.5f - 0.3f); break;
        }
        case 15: {  // Ice crystals
            float d = fabsf(Fr(u * 6) - 0.5f) + fabsf(Fr(v * 6) - 0.5f);
            float in = 0.5f + 0.5f * sinf(d * 14 - t * 2.2f); in *= in;
            float sp = Hh((int)(u * 60), (int)(v * 60), (int)(t * 4)) > 0.992f ? 1.0f : 0.0f;
            r = Cl(0.1f + in * 0.5f + sp); g = Cl(0.3f + in * 0.7f + sp); b = Cl(0.55f + in * 0.45f + sp); break;
        }
        case 16: {  // Equalizer bars
            const float NB = 16.0f;
            int col = (int)(u * NB);
            float fx = u * NB - col;
            float hgt = 0.15f + 0.85f * (0.5f + 0.5f * sinf(t * 3.0f + col * 0.9f + Hh(col) * 6.0f));
            float y = 1.0f - v, in = 0;
            if (fx > 0.12f && fx < 0.88f && y < hgt) in = 0.35f + 0.65f * (y / hgt);
            if (Fr(y * 14.0f) < 0.15f) in *= 0.25f;
            Hsv(0.33f * (1.0f - y), 1, 1, r, g, b); r *= in; g *= in; b *= in; break;
        }
        case 17: {  // Radar sweep
            float x = u - 0.5f, y = v - 0.5f;
            float rr = sqrtf(x * x + y * y), ang = atan2f(y, x);
            float sweep = fmodf(t * 1.4f, 2 * kPi) - kPi;
            float d = fmodf(sweep - ang + 4 * kPi, 2 * kPi);
            float trail = expf(-d * 1.6f);
            float ring = expf(-powf(Fr(rr * 10.0f) - 0.5f, 2.0f) * 70.0f) * 0.35f;
            float gv = Cl(trail * (rr < 0.7f ? 1.0f : 0.3f) + ring);
            r = gv * 0.15f; g = gv; b = gv * 0.35f; break;
        }
        case 18: {  // Hyperspace
            float x = u - 0.5f, y = v - 0.5f;
            float rr = sqrtf(x * x + y * y) * 2, ang = atan2f(y, x);
            int ai = (int)((ang + kPi) / (2 * kPi) * 48.0f);
            float sp = 0.5f + Hh(ai);
            float head = Fr(t * sp * 0.7f + Hh(ai, 3));
            float d = Fr(head - rr);
            float a = d < 0.3f ? powf(1 - d / 0.3f, 2.0f) : 0.0f;
            Hsv(0.55f + Hh(ai, 7) * 0.3f, 0.8f, 1, r, g, b); r *= a; g *= a; b *= a; break;
        }
        case 19: {  // Police lights
            int ph = (int)(t * 3.0f) & 1;
            bool left = (u < 0.5f);
            float flick = Fr(t * 14.0f) < 0.55f ? 1.0f : 0.25f;
            float on = ((left && ph == 0) || (!left && ph == 1)) ? flick : 0.12f;
            float fade = 0.75f + 0.25f * sinf(v * 16 + t * 6);
            if (left) { r = on * fade; g = 0; b = on * fade * 0.05f; }
            else { r = on * fade * 0.05f; g = on * fade * 0.3f; b = on * fade; }
            break;
        }
        case 20: {  // Rainbow spiral
            float x = u - 0.5f, y = v - 0.5f;
            float rr = sqrtf(x * x + y * y), ang = atan2f(y, x);
            Hsv(ang / (2 * kPi) * 2.0f + rr * 4.0f - t * 0.35f, 1, 0.55f + 0.45f * sinf(rr * 30 - t * 3), r, g, b); break;
        }
        case 21: {  // Ripples
            float d1 = sqrtf((u - 0.3f) * (u - 0.3f) + (v - 0.4f) * (v - 0.4f));
            float d2 = sqrtf((u - 0.75f) * (u - 0.75f) + (v - 0.65f) * (v - 0.65f));
            float s = sinf(d1 * 45 - t * 4) + sinf(d2 * 45 - t * 3.4f);
            float in = Cl(0.5f + 0.25f * s);
            Hsv(0.55f + 0.12f * s, 0.85f, in * in + 0.05f, r, g, b); break;
        }
        case 22: {  // Synthwave
            float bar = Fr(v * 10.0f - t * 0.4f);
            float cut = (v > 0.5f && bar < 0.08f + (v - 0.5f) * 0.5f) ? 0.0f : 1.0f;
            Hsv(0.78f - 0.70f * v, 0.9f, cut * (0.6f + 0.4f * (1 - v)), r, g, b); break;
        }
        case 23: {  // Neon bokeh
            int ci = (int)(u * 6), cj = (int)(v * 6);
            float h = Hh(ci, cj);
            float fu = u * 6 - ci, fv = v * 6 - cj;
            float cx = 0.5f + 0.12f * sinf(t * (0.8f + h) + h * 20), cy = 0.5f + 0.12f * cosf(t * (0.6f + h) + h * 13);
            float d = sqrtf((fu - cx) * (fu - cx) + (fv - cy) * (fv - cy));
            float rad = 0.2f + 0.1f * h;
            float a = Cl((rad - d) / 0.08f), glow = expf(-d * d * 20.0f) * 0.4f;
            float br = (a * 0.7f + glow) * (0.5f + 0.5f * sinf(t * 2 + h * 30)) + 0.03f;
            Hsv(h + t * 0.05f, 0.8f, 1, r, g, b); r *= br; g *= br; b *= br; break;
        }
        case 24: {  // Liquid chrome
            float val = sinf(u * 7 + t * 0.7f + sinf(v * 5 + t * 0.5f) * 2) + sinf(v * 9 - t * 0.6f + sinf(u * 4 - t * 0.4f) * 2);
            float m = Cl(0.5f + 0.25f * val); m = m * m * (3 - 2 * m);
            r = m * 0.85f + 0.05f; g = m * 0.9f + 0.06f; b = m + 0.1f; break;
        }
        case 25: {  // Acid plasma
            float val = sinf(u * 9 + t) + sinf(v * 7 - t * 1.2f) + sinf((u - v) * 8 + t * 0.8f);
            float fl = 0.5f + 0.5f * sinf(val * 1.2f);
            Hsv(0.18f + 0.1f * sinf(val), 1, fl * fl + 0.1f, r, g, b); break;
        }
        case 26: {  // Nebula
            float n = sinf(u * 4 + t * 0.2f) * sinf(v * 5 - t * 0.15f) + 0.5f * sinf((u + v) * 7 + t * 0.3f) + 0.3f * sinf(u * 13 - v * 9 + t * 0.5f);
            float m = Cl(0.5f + 0.4f * n);
            Hsv(0.72f + 0.15f * m, 0.8f, 0.12f + 0.7f * m * m, r, g, b);
            int cx = (int)(u * 50), cy = (int)(v * 50);
            if (Hh(cx, cy, 9) > 0.985f) { float tw = 0.5f + 0.5f * sinf(t * 3 + Hh(cx, cy) * 40); r += tw; g += tw; b += tw; }
            break;
        }
        case 27: {  // Gold & black bars with RGB edges
            float s = Fr((u * 2 + v) * 5.0f - t * 0.5f);
            float m = 0.5f + 0.5f * sinf(s * 2 * kPi);
            float bar = Cl(m * 3.0f - 1.0f);
            float edge = expf(-(m - 0.5f) * (m - 0.5f) * 160.0f);
            float er, eg, eb; Hsv(t * 0.15f + u, 1, 1, er, eg, eb);
            r = bar * 0.95f + er * edge * 0.7f; g = bar * 0.75f + eg * edge * 0.7f; b = bar * 0.2f + eb * edge * 0.7f; break;
        }
        case 28: {  // Circuit pulses
            const float N = 14.0f;
            int ci = (int)(u * N), cj = (int)(v * N);
            float h = Hh(ci, cj, 2);
            float fu = u * N - ci, fv = v * N - cj;
            bool horiz = h > 0.5f;
            float across = horiz ? fv : fu, along = horiz ? fu : fv;
            float line = expf(-(across - 0.5f) * (across - 0.5f) * 260.0f);
            float p = Fr(t * 0.5f + h * 7.0f);
            float pulse = expf(-(along - p) * (along - p) * 30.0f);
            float node = expf(-((fu - 0.5f) * (fu - 0.5f) + (fv - 0.5f) * (fv - 0.5f)) * 80.0f) * 0.6f;
            float in = Cl(line * (0.4f + pulse * 1.2f) + node * 0.6f);
            r = in * 0.1f; g = in * 0.9f; b = in; break;
        }
        case 29: {  // Electric waves
            float in = 0;
            for (int i = 0; i < 4; i++) {
                float y0 = 0.15f + 0.23f * i + 0.07f * sinf(u * 12 + t * 3 + i * 2.0f);
                float d = fabsf(v - y0);
                in += expf(-d * d * 2500.0f) + 0.2f * expf(-d * d * 150.0f);
            }
            in = Cl(in);
            r = Cl(in * 0.5f + in * in * 0.5f); g = Cl(in * 0.8f + in * in * 0.2f); b = in; break;
        }
        case 30: {  // Fire & Ice
            float fl = Cl((1 - v) * 1.4f + 0.35f * sinf(u * 18 + t * 6) * sinf(v * 9 - t * 5));
            float fr = fminf(1.0f, fl * 2), fg = Cl(fl * 2 - 0.7f), fb = Cl(fl * 3 - 2.4f);
            float ir = Cl(fl * 2 - 1.2f), ig = Cl(fl * 2 - 0.3f), ib = fminf(1.0f, fl * 2);
            float m = Cl((u - 0.5f) * 6.0f + 0.5f + 0.2f * sinf(t));
            r = fr + (ir - fr) * m; g = fg + (ig - fg) * m; b = fb + (ib - fb) * m; break;
        }
        case 31: {  // Disco tiles
            const float N = 8.0f;
            int ci = (int)(u * N), cj = (int)(v * N), step = (int)(t * 3.0f);
            float h = Hh(ci, cj, step);
            float fu = u * N - ci, fv = v * N - cj;
            float gap = (fu < 0.06f || fu > 0.94f || fv < 0.06f || fv > 0.94f) ? 0.0f : 1.0f;
            float br = (0.25f + 0.75f * (h > 0.5f ? 1.0f : 0.0f)) * gap;
            Hsv(Hh(ci, cj, step + 17), 1, br, r, g, b); break;
        }
        case 32: {  // Laser beams
            float x = u - 0.5f, y = v - 0.5f, ang = atan2f(y, x);
            for (int i = 0; i < 5; i++) {
                float ph = t * (0.6f + 0.15f * i) + i * 1.2566f;
                float d = sinf((ang - ph) * 0.5f);
                float beam = expf(-d * d * 220.0f);
                float cr, cg, cb; Hsv(i * 0.2f + t * 0.05f, 1, 1, cr, cg, cb);
                r += cr * beam; g += cg * beam; b += cb * beam;
            }
            float rr = sqrtf(x * x + y * y), core = expf(-rr * rr * 60.0f) * 0.6f;
            r += core; g += core; b += core; break;
        }
        case 33: {  // Caustics
            float c = sinf(u * 20 + sinf(v * 10 + t) * 2 + t) * sinf(v * 18 + sinf(u * 9 - t) * 2 - t * 1.2f);
            float in = expf(-fabsf(c) * 7.0f);
            r = Cl(0.02f + in * 0.4f); g = Cl(0.12f + in * 0.95f); b = Cl(0.25f + in); break;
        }
        case 34: {  // Hearts pulse
            float su = u * 3.0f, sv = v * 3.0f;
            float x = (su - floorf(su)) * 2 - 1, y = (sv - floorf(sv)) * 2 - 1;
            float pulse = 0.7f + 0.3f * sinf(t * 5 + floorf(su) * 1.7f + floorf(sv) * 2.3f);
            if (Shape(0, x, y)) { r = pulse; g = 0.1f * pulse; b = 0.35f * pulse; }
            else { r = 0.12f + 0.05f * sinf(t * 2 + u * 10); g = 0.01f; b = 0.06f; }
            break;
        }
        case 35: {  // Golden stars
            float su = u * 4.0f, sv = v * 4.0f;
            int ci = (int)floorf(su), cj = (int)floorf(sv);
            float x = (su - ci) * 2 - 1, y = (sv - cj) * 2 - 1;
            float tw = 0.65f + 0.35f * sinf(t * 4 + Hh(ci, cj) * 30);
            if (Shape(1, x, y)) { r = tw; g = tw * 0.78f; b = tw * 0.2f; }
            else { float bg = 0.05f + 0.03f * sinf(t + v * 8); r = bg; g = bg * 0.8f; b = bg * 0.2f; }
            break;
        }
        default: {
            int row = (int)(v * 16);
            float sp = 0.4f + Hh(row) * 0.8f;
            float head = fmodf(t * sp + Hh(row, 5), 1.0f);
            float d = fmodf(head - u + 1.0f, 1.0f);
            float a = d < 0.3f ? powf(1 - d / 0.3f, 2.0f) : 0;
            Hsv(Hh(row, 9) + t * 0.1f, 1, 1, r, g, b); r *= a; g *= a; b *= a; break;
        }
    }
    return Pack(r, g, b);
}
static bool EnsureDyn() {
    if (g_dynTex) return true;
    g_dynRaster = RwRasterCreate(DYN_SIZE, DYN_SIZE, 32, rwRASTERTYPETEXTURE | rwRASTERFORMAT8888);
    if (!g_dynRaster) return false;
    g_dynTex = RwTextureCreate(g_dynRaster);
    if (!g_dynTex) return false;
    strncpy(g_dynTex->name, "bt_dyn", 31);
    RwTextureSetFilterMode(g_dynTex, rwFILTERLINEAR);
    RwTextureSetAddressing(g_dynTex, rwTEXTUREADDRESSWRAP);
    return true;
}
static void UpdateDyn() {
    if (!g_dynRaster) return;
    float t = CTimer::m_snTimeInMilliseconds / 1000.0f;
    RwUInt8* px = RwRasterLock(g_dynRaster, 0, rwRASTERLOCKWRITE);
    if (!px) return;
    int stride = RwRasterGetStride(g_dynRaster);
    for (int y = 0; y < DYN_SIZE; y++) {
        uint32_t* row = (uint32_t*)(px + y * stride);
        for (int x = 0; x < DYN_SIZE; x++)
            row[x] = Pixel(g_design, (x + 0.5f) / DYN_SIZE, (y + 0.5f) / DYN_SIZE, t);
    }
    RwRasterUnlock(g_dynRaster);
}

// ---------------- apply / restore ----------------
static void ApplyAll() {
    if (!g_veh) return;
    RwTexture* tex = nullptr;
    bool glow = false;
    if (g_mode == 1) tex = CurTex();
    else if (g_mode == 2) { if (EnsureDyn()) { UpdateDyn(); tex = g_dynTex; } glow = g_design >= FIRST_GLOW; }
    if (!tex) return;
    RwSurfaceProperties glowProps;
    glowProps.ambient = 2.5f; glowProps.specular = 0.0f; glowProps.diffuse = 0.0f;
    for (auto& r : g_recs) {
        if (r.on) {
            RpMaterialSetTexture(r.mat, tex);
            if (glow) RpMaterialSetSurfaceProperties(r.mat, &glowProps);
            else RpMaterialSetSurfaceProperties(r.mat, &r.origProps);
        } else {
            if (RpMaterialGetTexture(r.mat) != r.origTex) RpMaterialSetTexture(r.mat, r.origTex);
            RpMaterialSetSurfaceProperties(r.mat, &r.origProps);
        }
    }
}
static void Release() {
    if (g_veh) {
        bool ok = VehicleAlive(g_veh) && g_veh->m_nModelIndex == g_vehModel;
        if (ok) {
            for (auto& r : g_recs) {
                RpMaterialSetTexture(r.mat, r.origTex);
                RpMaterialSetSurfaceProperties(r.mat, &r.origProps);
                if (r.origTex) RwTextureDestroy(r.origTex);
            }
            g_veh->m_nPrimaryColor = g_origCols[0];
            g_veh->m_nSecondaryColor = g_origCols[1];
            g_veh->m_nTertiaryColor = g_origCols[2];
            g_veh->m_nQuaternaryColor = g_origCols[3];
        } else {
            Log("vehicle gone, dropping %d records without restore", (int)g_recs.size());
        }
    }
    g_recs.clear();
    g_veh = nullptr;
    g_vehModel = -1;
}
static void Acquire(CVehicle* v) {
    if (!v || !v->m_pRwClump) return;
    Log("== analyzing vehicle model %d ==", (int)v->m_nModelIndex);
    g_recs.clear();
    RpClumpForAllAtomics(v->m_pRwClump, AtomCB, nullptr);
    int onCnt = 0;
    for (auto& r : g_recs) if (r.on) onCnt++;
    Log("materials found: %d (painted: %d)", (int)g_recs.size(), onCnt);
    g_partPage = 0;
    g_veh = v;
    g_vehModel = v->m_nModelIndex;
    g_origCols[0] = v->m_nPrimaryColor; g_origCols[1] = v->m_nSecondaryColor;
    g_origCols[2] = v->m_nTertiaryColor; g_origCols[3] = v->m_nQuaternaryColor;
    // white paint so the texture is not tinted by the car color
    v->m_nPrimaryColor = v->m_nSecondaryColor = v->m_nTertiaryColor = v->m_nQuaternaryColor = 1;
    ApplyAll();
}

// ---------------- input ----------------
static bool Pressed(int vk) {
    static bool prev[256];
    bool now = (GetAsyncKeyState(vk) & 0x8000) != 0;
    bool hit = now && !prev[vk & 255];
    prev[vk & 255] = now;
    return hit;
}

// typing the letters P, R, S one after another (like a cheat code) toggles the menu
static bool CheatTyped() {
    static bool prev[256];
    static char buf[3] = {0, 0, 0};
    bool hit = false;
    for (int vk = 'A'; vk <= 'Z'; vk++) {
        bool now = (GetAsyncKeyState(vk) & 0x8000) != 0;
        if (now && !prev[vk]) {
            buf[0] = buf[1]; buf[1] = buf[2]; buf[2] = (char)vk;
            if (buf[0] == 'P' && buf[1] == 'R' && buf[2] == 'S') {
                hit = true;
                buf[0] = buf[1] = buf[2] = 0;
            }
        }
        prev[vk] = now;
    }
    return hit;
}

// ---------------- menu state ----------------
static bool g_menu = false;
static float g_cx = 0, g_cy = 0;           // virtual cursor (screen px)
static bool g_lmbPrev = true, g_click = false;
static char g_txd[32] = "";
static bool g_focus = false;
static char g_status[96] = "";
static unsigned g_statusT = 0;
static const float MOUSE_SENS = 1.0f;      // tune if cursor feels too slow/fast
static int  g_designPage = 0;             // page of the animated-design list in the menu
static bool g_glow = true;                 // light from the body into the world (F10 / menu button)
static bool g_invert = false;              // false = normal mouse, true = inverted (both axes); F9 or menu button

static float SW() { return (float)RsGlobal.maximumWidth; }
static float SH() { return (float)RsGlobal.maximumHeight; }
static void Status(const char* fmt, ...) {
    va_list a; va_start(a, fmt);
    vsnprintf(g_status, sizeof(g_status), fmt, a);
    va_end(a);
    g_statusT = CTimer::m_snTimeInMilliseconds;
}

// ---------------- actions ----------------
static void SetMode(int m) {
    g_mode = m;
    if (m == 0) { if (g_veh) Release(); return; }
    if (m == 1 && !CurTex()) g_navPending = 1;
    ApplyAll();
}
static void Nav(int n) { g_navPending += n; }
// works off queued prev/next steps with a small time and TXD-load budget so the game never freezes
static void PumpNav() {
    g_opensFrame = 0;
    if (g_navPending == 0) return;
    DWORD t0 = GetTickCount();
    int dir = g_navPending > 0 ? 1 : -1;
    bool moved = false;
    while (g_navPending != 0 && GetTickCount() - t0 < 12) {
        int r = Step(dir);
        if (r == 1) { g_navPending -= dir; moved = true; }
        else if (r == 0) { g_navPending = 0; break; }
        else break;
    }
    if (moved) ApplyAll();
}
static void GoTxd() {
    if (!g_txd[0]) { Status("type a TXD name first"); return; }
    if (!CTxdStore::ms_pTxdPool) return;
    g_nSlots = CTxdStore::ms_pTxdPool->m_nSize;
    g_navPending = 0;
    int s = CTxdStore::FindTxdSlot(g_txd);
    if (s < 0 || !SlotValid(s)) { Status("TXD '%s' not found", g_txd); return; }
    OpenSlot(s);
    g_idx = 0;
    if (g_tex.empty()) { Status("TXD '%s' has no textures / could not load", g_txd); return; }
    g_mode = 1;
    ApplyAll();
    Status("loaded TXD '%s' (%d textures)", g_txd, (int)g_tex.size());
}
static void ToggleMenu() {
    g_menu = !g_menu;
    if (g_menu) {
        g_cx = SW() * 0.5f; g_cy = SH() * 0.5f;
        g_lmbPrev = true; g_focus = false;
    } else {
        g_focus = false;
        CPad::GetPad(0)->DisablePlayerControls = false;
    }
}

// plugin-sdk's CMouseControllerState has no members named X/Y; access the two mouse-delta floats by
// their fixed GTA SA layout: 7 bools + pad (8 bytes), float wheel (+8), float X (+12), float Y (+16)
static float& MX(CMouseControllerState& m) { return *(float*)((char*)&m + 12); }
static float& MY(CMouseControllerState& m) { return *(float*)((char*)&m + 16); }

// ---------------- mouse (own virtual cursor, camera frozen) ----------------
static void UpdateMouse() {
    auto& m = CPad::NewMouseControllerState;
    float sgn = g_invert ? -1.0f : 1.0f;
    g_cx += MX(m) * MOUSE_SENS * sgn;
    g_cy += MY(m) * MOUSE_SENS * sgn;
    if (g_cx < 0) g_cx = 0; if (g_cx > SW() - 1) g_cx = SW() - 1;
    if (g_cy < 0) g_cy = 0; if (g_cy > SH() - 1) g_cy = SH() - 1;
    bool lmb = m.lmb;
    g_click = lmb && !g_lmbPrev;
    g_lmbPrev = lmb;
    MX(m) = MY(m) = 0; m.lmb = m.rmb = m.mmb = false;  // camera/shoot get nothing
    auto& t = CPad::PCTempMouseControllerState;
    MX(t) = MY(t) = 0; t.lmb = t.rmb = t.mmb = false;
    CPad::GetPad(0)->DisablePlayerControls = true;
}
static void HandleTyping() {
    if (!g_focus) return;
    size_t n = strlen(g_txd);
    for (int vk = 'A'; vk <= 'Z'; vk++)
        if (Pressed(vk) && n < 24) g_txd[n++] = (char)(vk - 'A' + 'a');
    for (int vk = '0'; vk <= '9'; vk++)
        if (Pressed(vk) && n < 24) g_txd[n++] = (char)vk;
    if (Pressed(VK_OEM_MINUS) && n < 24) g_txd[n++] = (GetAsyncKeyState(VK_SHIFT) & 0x8000) ? '_' : '-';
    if (Pressed(VK_BACK) && n > 0) n--;
    g_txd[n] = 0;
    if (Pressed(VK_RETURN)) GoTxd();
    if (Pressed(VK_ESCAPE)) g_focus = false;
}

// ---------------- drawing helpers ----------------
#define C_GOLD    CRGBA(212, 175, 55, 255)
#define C_GOLD_LT CRGBA(255, 226, 130, 255)
#define C_GOLD_DK CRGBA(120, 95, 28, 255)
#define C_TXT     CRGBA(236, 220, 170, 255)

static float NowSec() { return CTimer::m_snTimeInMilliseconds / 1000.0f; }
static CRGBA Mix(CRGBA a, CRGBA b, float t) {
    return CRGBA((unsigned char)(a.r + (b.r - a.r) * t), (unsigned char)(a.g + (b.g - a.g) * t),
                 (unsigned char)(a.b + (b.b - a.b) * t), (unsigned char)(a.a + (b.a - a.a) * t));
}
static CRGBA HueCol(float h, unsigned char a = 255, float s = 1.0f) {
    float r, g, b; Hsv(h, s, 1.0f, r, g, b);
    return CRGBA((unsigned char)(r * 255), (unsigned char)(g * 255), (unsigned char)(b * 255), a);
}
static void FillRect(float x, float y, float w, float h, CRGBA c) {
    CSprite2d::DrawRect(CRect(x, y + h, x + w, y), c);
}
static void VGrad(float x, float y, float w, float h, CRGBA a, CRGBA b, int bands = 18) {
    float bh = h / bands;
    for (int i = 0; i < bands; i++)
        FillRect(x, y + i * bh, w, bh + 0.6f, Mix(a, b, (float)i / (float)(bands - 1)));
}
static void TextF(float x, float y, const char* s, CRGBA col, float scale, bool pricedown, int edge) {
    char buf[200];
    strncpy(buf, s, sizeof(buf) - 1); buf[sizeof(buf) - 1] = 0;
    if (pricedown) CFont::SetFontStyle(FONT_PRICEDOWN); else CFont::SetFontStyle(FONT_SUBTITLES);
    CFont::SetScale(0.36f * scale * SW() / 640.0f, 0.78f * scale * SH() / 448.0f);
    CFont::SetColor(col);
    CFont::SetOrientation(ALIGN_LEFT);
    CFont::SetEdge(edge);
    CFont::SetWrapx(SW());
    CFont::PrintString(x, y, buf);
}
static void Text(float x, float y, const char* s, CRGBA col, float scale = 1.0f) {
    TextF(x, y, s, col, scale, false, 1);
}
// per-letter RGB text: longer prefixes are drawn first, shorter prefixes are drawn over them in
// their own colour, so every letter ends up with a different hue (no glyph width needed)
static void TextRainbow(float x, float y, const char* s, float scale) {
    int n = (int)strlen(s); if (n > 60) n = 60;
    const int G = 2;
    int m = (n + G - 1) / G;
    float t = NowSec();
    char buf[64];
    for (int g = m; g >= 1; g--) {
        int len = g * G; if (len > n) len = n;
        memcpy(buf, s, len); buf[len] = 0;
        TextF(x, y, buf, HueCol((float)(g - 1) / (float)m * 0.85f - t * 0.35f, 255, 0.85f), scale, false, 0);
    }
}
// rotating RGB border: a rainbow that travels around the perimeter
static void RgbBorder(float x, float y, float w, float h, float th) {
    float t = NowSec();
    float L = 2 * (w + h);
    int n = (int)(L / 6.0f); if (n < 16) n = 16;
    float seg = L / n;
    for (int i = 0; i < n; i++) {
        float p = i * seg;
        CRGBA c = HueCol(p / L - t * 0.5f);
        float sx, sy, sw, sh;
        if (p < w)                  { sx = x + p;                 sy = y;                       sw = seg + 0.6f; sh = th; }
        else if (p < w + h)         { sx = x + w - th;            sy = y + (p - w);             sw = th;         sh = seg + 0.6f; }
        else if (p < 2 * w + h)     { sx = x + w - (p - w - h) - seg; sy = y + h - th;          sw = seg + 0.6f; sh = th; }
        else                        { sx = x;                     sy = y + h - (p - 2 * w - h) - seg; sw = th;     sh = seg + 0.6f; }
        FillRect(sx, sy, sw, sh, c);
    }
}
static void RgbLine(float x, float y, float w, float th) {
    float t = NowSec();
    int n = (int)(w / 5.0f); if (n < 6) n = 6;
    float seg = w / n;
    for (int i = 0; i < n; i++)
        FillRect(x + i * seg, y, seg + 0.6f, th, HueCol((float)i / (float)n * 0.9f - t * 0.5f));
}
static void GoldBorder(float x, float y, float w, float h, float th, CRGBA c) {
    FillRect(x, y, w, th, c);
    FillRect(x, y + h - th, w, th, c);
    FillRect(x, y, th, h, c);
    FillRect(x + w - th, y, th, h, c);
}
static bool Hover(float x, float y, float w, float h) {
    return g_cx >= x && g_cx <= x + w && g_cy >= y && g_cy <= y + h;
}
// black glass panel: soft RGB glow outside, black->dark-gold gradient, gold frame, thin RGB inner line, gold corners
static void Panel(float x, float y, float w, float h, bool glow) {
    float t = NowSec();
    if (glow)
        for (int k = 4; k >= 1; k--) {
            float e = k * 3.0f;
            FillRect(x - e, y - e, w + 2 * e, h + 2 * e, HueCol(t * 0.15f, (unsigned char)(10 + (5 - k) * 4)));
        }
    VGrad(x, y, w, h, CRGBA(9, 9, 11, 238), CRGBA(24, 18, 6, 238));
    GoldBorder(x, y, w, h, 1.2f, C_GOLD);
    RgbBorder(x + 3, y + 3, w - 6, h - 6, 1.2f);
    float len = 16.0f, th = 2.4f;
    CRGBA g = C_GOLD_LT;
    FillRect(x - 1, y - 1, len, th, g);                    FillRect(x - 1, y - 1, th, len, g);
    FillRect(x + w - len + 1, y - 1, len, th, g);          FillRect(x + w - th + 1, y - 1, th, len, g);
    FillRect(x - 1, y + h - th + 1, len, th, g);           FillRect(x - 1, y + h - len + 1, th, len, g);
    FillRect(x + w - len + 1, y + h - th + 1, len, th, g); FillRect(x + w - th + 1, y + h - len + 1, th, len, g);
}
static bool Button(const char* label, float x, float y, float w, float h, bool selected) {
    bool hov = Hover(x, y, w, h);
    CRGBA bg = selected ? CRGBA(30, 24, 8, 242) : (hov ? CRGBA(28, 23, 10, 242) : CRGBA(12, 12, 14, 232));
    FillRect(x, y, w, h, bg);
    if (selected) FillRect(x, y, w, h * 0.5f, CRGBA(212, 175, 55, 34));
    GoldBorder(x, y, w, h, 1.0f, (selected || hov) ? C_GOLD_LT : C_GOLD_DK);
    if (selected || hov) RgbLine(x + 2, y + h - 3.0f, w - 4, 1.6f);
    if (selected) FillRect(x, y, 3.0f, h, C_GOLD);
    CRGBA tc = selected ? C_GOLD_LT : (hov ? CRGBA(255, 255, 255, 255) : CRGBA(222, 222, 226, 255));
    Text(x + 10, y + h * 0.18f, label, tc, 0.85f);
    return hov && g_click;
}

// Watch Dogs 2 style name: RGB-split ghosts, random glitch bursts, jitter and flicker
static void DrawNameText(float x, float y) {
    unsigned ms = CTimer::m_snTimeInMilliseconds;
    float t = ms / 1000.0f, u = SW() / 1280.0f;
    float ph = fmodf(t, 2.4f);
    bool burst = ph < 0.22f || (ph > 1.1f && ph < 1.18f);
    int k = (int)(ms / 45);
    float amp = (1.4f + 0.8f * sinf(t * 3.0f)) * u;
    float jx = 0, jy = 0;
    if (burst) { amp += (3.0f + 9.0f * Hh(k)) * u; jx = (Hh(k, 1) - 0.5f) * 10.0f * u; jy = (Hh(k, 2) - 0.5f) * 3.0f * u; }
    unsigned char a = (Hh(k, 3) > 0.94f) ? 190 : 255;
    TextF(x - amp + jx, y, "Parsa Rsi", CRGBA(0, 255, 255, 210), 1.7f, true, 0);
    TextF(x + amp + jx, y + jy, "Parsa Rsi", CRGBA(255, 0, 90, 210), 1.7f, true, 0);
    TextF(x + jx * 0.5f, y, "Parsa Rsi", CRGBA(255, 255, 255, a), 1.7f, true, 0);
}
static void DrawHeader(float px, float py, float pw, float hh, float pad) {
    float H = SH(), u = SW() / 1280.0f, t = NowSec();
    unsigned ms = CTimer::m_snTimeInMilliseconds;
    FillRect(px + 1, py + 1, pw - 2, hh, CRGBA(212, 175, 55, 16));
    TextRainbow(px + pad, py + H * 0.014f, "texture menu create by :", 0.8f);
    CFont::DrawFonts();
    float ny = py + H * 0.043f;
    DrawNameText(px + pad + 2, ny);
    CFont::DrawFonts();
    // everything below is drawn after the text has been flushed, so it lays over the letters
    for (float yy = py + 2; yy < py + hh; yy += 3.0f) FillRect(px + 1, yy, pw - 2, 1.0f, CRGBA(0, 0, 0, 70));  // scanlines
    float ph = fmodf(t, 2.4f);
    bool burst = ph < 0.22f || (ph > 1.1f && ph < 1.18f);
    if (burst) {
        int k = (int)(ms / 45);
        float nh = H * 0.062f;
        for (int i = 0; i < 3; i++) {
            float by = ny + Hh(k, 10 + i) * nh;
            float bx = px + pad + Hh(k, 30 + i) * pw * 0.25f;
            float bw = (0.08f + 0.22f * Hh(k, 20 + i)) * pw;
            float bh = (1.0f + 3.0f * Hh(k, 40 + i)) * u;
            CRGBA c = (i == 0) ? CRGBA(0, 255, 255, 150) : (i == 1 ? CRGBA(255, 0, 90, 150) : CRGBA(0, 0, 0, 255));
            FillRect(bx, by, bw, bh, c);
        }
        for (int i = 0; i < 6; i++) {
            float bx = px + pad + Hh(k, 50 + i) * pw * 0.45f, by = ny + Hh(k, 60 + i) * nh;
            FillRect(bx, by, (2.0f + 5.0f * Hh(k, 70 + i)) * u, (2.0f + 3.0f * Hh(k, 80 + i)) * u, HueCol(Hh(k, 90 + i), 200));
        }
    }
    // divider: gold hairline, travelling highlight, RGB line
    float dy = py + hh;
    FillRect(px + pad, dy, pw - 2 * pad, 1.2f, C_GOLD);
    float sx = px + pad + (fmodf(t * 0.45f, 1.4f) - 0.2f) * (pw - 2 * pad);
    float sw = 0.2f * (pw - 2 * pad);
    float x0 = sx < px + pad ? px + pad : sx;
    float x1 = (sx + sw) > (px + pw - pad) ? (px + pw - pad) : (sx + sw);
    if (x1 > x0) FillRect(x0, dy - 0.4f, x1 - x0, 2.0f, C_GOLD_LT);
    RgbLine(px + pad, dy + 3.0f, pw - 2 * pad, 1.6f);
}

// right-hand panel: every part/material found on the car, which ones are painted, click to toggle
static void DrawParts(float px, float py, float pw, float ph) {
    if (g_recs.empty() || !g_veh || g_mode == 0) return;
    float W = SW(), H = SH();
    float x0 = px + pw + 10.0f;
    float w0 = W - x0 - 10.0f;
    if (w0 < 80.0f) return;
    float pad = 10.0f, gap = 6.0f, bh = H * 0.045f, rowH = H * 0.036f;
    Panel(x0, py, w0, ph, false);
    int total = (int)g_recs.size(), onCnt = 0;
    for (auto& r : g_recs) if (r.on) onCnt++;
    char head[64];
    sprintf(head, "Parts  %d / %d painted", onCnt, total);
    Text(x0 + pad, py + 8, head, C_GOLD_LT, 0.85f);
    FillRect(x0 + pad, py + H * 0.05f, w0 - 2 * pad, 1.0f, C_GOLD_DK);
    float y = py + H * 0.062f;
    float by = py + ph - bh - pad;
    float listBottom = by - bh - gap - gap;
    int perPage = (int)((listBottom - y) / rowH);
    if (perPage < 1) perPage = 1;
    int pages = (total + perPage - 1) / perPage;
    if (g_partPage >= pages) g_partPage = pages - 1;
    if (g_partPage < 0) g_partPage = 0;
    const char* applied = (g_mode == 1) ? (CurTex() ? CurTex()->name : "-") : DESIGN_NAME[g_design];
    for (int i = g_partPage * perPage; i < total && i < (g_partPage + 1) * perPage; i++) {
        MatRec& r = g_recs[i];
        bool hov = Hover(x0 + pad, y, w0 - 2 * pad, rowH - 2);
        if (hov) { FillRect(x0 + pad, y, w0 - 2 * pad, rowH - 2, CRGBA(212, 175, 55, 30)); FillRect(x0 + pad, y, 2.0f, rowH - 2, C_GOLD); }
        float s = rowH * 0.34f, sy = y + (rowH - 2 - s) * 0.5f;
        if (r.on) FillRect(x0 + pad + 6, sy, s, s, C_GOLD_LT);
        else GoldBorder(x0 + pad + 6, sy, s, s, 1.0f, C_GOLD_DK);
        char line[120];
        if (r.on) sprintf(line, "%.16s > %.12s", r.frame, applied);
        else sprintf(line, "%.16s (%s)", r.frame, r.why[0] ? r.why : "off");
        Text(x0 + pad + 6 + s + 8, y + 1, line, r.on ? C_GOLD_LT : CRGBA(150, 150, 156, 255), 0.7f);
        if (hov && g_click && r.canUse) { r.on = !r.on; ApplyAll(); }
        y += rowH;
    }
    float bw2 = (w0 - 2 * pad - gap) / 2;
    if (Button("< Page", x0 + pad, by - bh - gap, bw2, bh, false)) g_partPage--;
    if (Button("Page >", x0 + pad + bw2 + gap, by - bh - gap, bw2, bh, false)) g_partPage++;
    if (Button("All on", x0 + pad, by, bw2, bh, false)) { for (auto& r : g_recs) if (r.canUse) r.on = true; ApplyAll(); }
    if (Button("Reset", x0 + pad + bw2 + gap, by, bw2, bh, false)) { for (auto& r : g_recs) r.on = r.autoOn; ApplyAll(); }
}

static void DrawMenu() {
    static bool logged = false;
    if (!logged) { logged = true; Log("menu drawn"); }
    float W = SW(), H = SH();
    float pw = W * 0.48f, ph = H * 0.74f, px = (W - pw) * 0.5f, py = (H - ph) * 0.5f;
    float pad = 14.0f, gap = 8.0f, bh = H * 0.058f, hh = H * 0.115f;
    Panel(px, py, pw, ph, true);
    DrawHeader(px, py, pw, hh, pad);

    float y = py + hh + H * 0.02f;
    float bw3 = (pw - 2 * pad - 2 * gap) / 3;
    if (Button("Off", px + pad, y, bw3, bh, g_mode == 0)) SetMode(0);
    if (Button("1: Game textures", px + pad + bw3 + gap, y, bw3, bh, g_mode == 1)) SetMode(1);
    if (Button("2: Animated paint", px + pad + 2 * (bw3 + gap), y, bw3, bh, g_mode == 2)) SetMode(2);
    y += bh + H * 0.03f;

    // clicking anywhere except the text field removes focus
    float inW = pw * 0.58f;
    bool inHover = false;

    if (g_mode == 1) {
        char info[120];
        RwTexture* t = CurTex();
        sprintf(info, "TXD slot %d | %s (%d/%d)%s", g_slot, t ? t->name : "-", g_idx + 1, (int)g_tex.size(), g_navPending ? "  ..." : "");
        Text(px + pad, y, info, C_TXT, 0.9f);
        y += H * 0.05f;
        float bw4 = (pw - 2 * pad - 3 * gap) / 4;
        if (Button("<< 100", px + pad, y, bw4, bh, false)) Nav(-100);
        if (Button("< Prev", px + pad + (bw4 + gap), y, bw4, bh, false)) Nav(-1);
        if (Button("Next >", px + pad + 2 * (bw4 + gap), y, bw4, bh, false)) Nav(1);
        if (Button("100 >>", px + pad + 3 * (bw4 + gap), y, bw4, bh, false)) Nav(100);
        y += bh + H * 0.035f;
        Text(px + pad, y, "Type a TXD name, then click Go (or press Enter):", C_TXT, 0.85f);
        y += H * 0.045f;
        inHover = Hover(px + pad, y, inW, bh);
        if (inHover && g_click) g_focus = true;
        FillRect(px + pad, y, inW, bh, CRGBA(0, 0, 0, 240));
        if (g_focus) RgbBorder(px + pad, y, inW, bh, 2.2f); else GoldBorder(px + pad, y, inW, bh, 1.0f, C_GOLD_DK);
        char shown[48];
        bool blink = ((CTimer::m_snTimeInMilliseconds / 500) & 1) != 0;
        sprintf(shown, "%s%s", g_txd, (g_focus && blink) ? "_" : "");
        Text(px + pad + 8, y + bh * 0.18f, shown, CRGBA(255, 255, 255, 255), 0.9f);
        if (Button("Go", px + pad + inW + gap, y, pw - 2 * pad - inW - gap, bh, false)) GoTxd();
    } else if (g_mode == 2) {
        Text(px + pad, y, "Pick a design (no images, pure code):", C_TXT, 0.9f);
        y += H * 0.05f;
        int pages = (N_DESIGNS + 8) / 9;
        static int lastD = -1;
        if (g_design != lastD) { g_designPage = g_design / 9; lastD = g_design; }
        if (g_designPage >= pages) g_designPage = pages - 1;
        if (g_designPage < 0) g_designPage = 0;
        for (int j = 0; j < 9; j++) {
            int i = g_designPage * 9 + j;
            if (i >= N_DESIGNS) break;
            int cx = j % 3, cy = j / 3;
            if (Button(DESIGN_NAME[i], px + pad + cx * (bw3 + gap), y + cy * (bh + gap), bw3, bh, g_design == i)) {
                g_design = i;
                ApplyAll();
            }
        }
        float ry = y + 3 * (bh + gap);
        if (Button("< Prev", px + pad, ry, bw3, bh, false)) g_designPage = (g_designPage + pages - 1) % pages;
        char pg[32];
        sprintf(pg, "Page %d / %d  (%d designs)", g_designPage + 1, pages, N_DESIGNS);
        GoldBorder(px + pad + bw3 + gap, ry, bw3, bh, 1.0f, C_GOLD_DK);
        Text(px + pad + bw3 + gap + 10, ry + bh * 0.18f, pg, C_GOLD_LT, 0.7f);
        if (Button("Next >", px + pad + 2 * (bw3 + gap), ry, bw3, bh, false)) g_designPage = (g_designPage + 1) % pages;
    } else {
        Text(px + pad, y, "Choose a category above. Get into a car to see the result.", C_TXT, 0.85f);
    }
    if (g_click && !inHover) g_focus = false;

    // status line + bottom row (mouse mode, close)
    unsigned now = CTimer::m_snTimeInMilliseconds;
    float fy = py + ph - bh - pad;
    if (g_status[0] && now - g_statusT < 6000)
        Text(px + pad, fy - H * 0.04f, g_status, C_GOLD_LT, 0.85f);
    else if (!g_veh && g_mode != 0)
        Text(px + pad, fy - H * 0.04f, "Get into a car to apply.", C_GOLD_LT, 0.85f);
    if (Button(g_invert ? "Mouse: Inverted" : "Mouse: Normal", px + pad, fy, bw3, bh, g_invert)) {
        g_invert = !g_invert;
        Status(g_invert ? "mouse inverted (F9 toggles)" : "mouse normal (F9 toggles)");
    }
    if (g_mode == 2 && Button(g_glow ? "Glow light: On" : "Glow light: Off", px + pad + bw3 + gap, fy, bw3, bh, g_glow)) {
        g_glow = !g_glow;
        Status(g_glow ? "glow light on (F10 toggles)" : "glow light off (F10 toggles)");
    }
    if (Button("Close  (type PRS)", px + pw - pad - bw3, fy, bw3, bh, false)) ToggleMenu();

    DrawParts(px, py, pw, ph);

    // cursor: gold cross with black outline and its own RGB ring
    FillRect(g_cx - 2, g_cy - 10, 4, 20, CRGBA(0, 0, 0, 255));
    FillRect(g_cx - 10, g_cy - 2, 20, 4, CRGBA(0, 0, 0, 255));
    FillRect(g_cx - 1, g_cy - 9, 2, 18, C_GOLD_LT);
    FillRect(g_cx - 9, g_cy - 1, 18, 2, C_GOLD_LT);
    RgbBorder(g_cx - 6, g_cy - 6, 12, 12, 1.5f);
    g_click = false;
}

// light that streams out of the body into the game world; its colour follows the current design
static void AddGlowLights() {
    if (!g_veh || !g_glow || g_mode != 2) return;
    float t = CTimer::m_snTimeInMilliseconds / 1000.0f;
    float ar = 0, ag = 0, ab = 0;
    for (int i = 0; i < 12; i++) {
        uint32_t c = Pixel(g_design, ((i % 4) + 0.5f) / 4.0f, ((i / 4) + 0.5f) / 3.0f, t);
        ar += ((c >> 16) & 255) / 255.0f; ag += ((c >> 8) & 255) / 255.0f; ab += (c & 255) / 255.0f;
    }
    ar /= 12; ag /= 12; ab /= 12;
    float m = fmaxf(ar, fmaxf(ag, ab));
    float cr, cg, cb;
    if (m < 0.04f) Hsv(t * 0.2f, 1, 1, cr, cg, cb);
    else {
        float k = 0.35f + 0.65f * Cl(m * 3.0f);
        cr = ar / m * k; cg = ag / m * k; cb = ab / m * k;
    }
    float pulse = 0.9f + 0.1f * sinf(t * 6.0f);
    cr *= pulse; cg *= pulse; cb *= pulse;
    CVector p = g_veh->GetPosition();
    CVector zero(0, 0, 0);
    CPointLights::AddLight(0, CVector(p.x, p.y, p.z + 0.6f), zero, 14.0f, cr, cg, cb, 0, false, nullptr);
    CPointLights::AddLight(0, CVector(p.x + 2.4f, p.y, p.z), zero, 9.0f, cr, cg, cb, 0, false, nullptr);
    CPointLights::AddLight(0, CVector(p.x - 2.4f, p.y, p.z), zero, 9.0f, cr, cg, cb, 0, false, nullptr);
    CPointLights::AddLight(0, CVector(p.x, p.y + 2.4f, p.z), zero, 9.0f, cr, cg, cb, 0, false, nullptr);
    CPointLights::AddLight(0, CVector(p.x, p.y - 2.4f, p.z), zero, 9.0f, cr, cg, cb, 0, false, nullptr);
    CPointLights::AddLight(0, CVector(p.x, p.y, p.z - 0.4f), zero, 7.0f, cr, cg, cb, 0, false, nullptr);
}

static bool g_procRan = false;
static void Process() {
    g_procRan = true;
    static bool firstP = true;
    if (firstP) { firstP = false; Log("Process running"); }
    PumpNav();
    if (Pressed(VK_F10)) { g_glow = !g_glow; Status(g_glow ? "glow light on (F10 toggles)" : "glow light off (F10 toggles)"); }
    if (Pressed(VK_F9)) { g_invert = !g_invert; Status(g_invert ? "mouse inverted (F9 toggles)" : "mouse normal (F9 toggles)"); }
    CVehicle* v = FindPlayerVehicle(-1, false);
    bool cheat = CheatTyped();
    if (cheat && !g_focus) { ToggleMenu(); Log("PRS typed, menu=%d", g_menu ? 1 : 0); }
    if (g_menu) {
        UpdateMouse();
        HandleTyping();
    } else {
        if (Pressed(VK_NUMPAD0)) SetMode(0);
        if (g_mode == 1) {
            if (Pressed(VK_NUMPAD6)) Nav(1);
            if (Pressed(VK_NUMPAD4)) Nav(-1);
            if (Pressed(VK_NUMPAD9)) Nav(100);
            if (Pressed(VK_NUMPAD3)) Nav(-100);
        } else if (g_mode == 2) {
            if (Pressed(VK_NUMPAD6)) { g_design = (g_design + 1) % N_DESIGNS; ApplyAll(); }
            if (Pressed(VK_NUMPAD4)) { g_design = (g_design + N_DESIGNS - 1) % N_DESIGNS; ApplyAll(); }
        }
    }
    if (g_mode == 0) {
        if (g_veh) Release();
        return;
    }
    if (v && v != g_veh) {            // got into a (different) car
        Release();
        Acquire(v);
        return;
    }
    if (!v && g_veh && (!VehicleAlive(g_veh) || g_veh->m_nModelIndex != g_vehModel || !g_veh->m_pRwClump)) {
        Release();                    // on foot and the car is gone; otherwise the paint stays on it
        return;
    }
    if (!g_veh) return;
    if (g_mode == 2) {
        if (++g_frame % DYN_EVERY == 0) UpdateDyn();
        AddGlowLights();
    }
}

static void DrawHud() {
    static bool firstD = true;
    if (firstD) { firstD = false; Log("DrawHud running"); }
    // gameProcessEvent does not fire on this setup, so run the logic from the HUD event when needed
    if (!g_procRan) Process();
    g_procRan = false;
    if (g_menu) {
        // camera must stay frozen even if the pad was refreshed after Process
        auto& m = CPad::NewMouseControllerState;
        MX(m) = MY(m) = 0;
        DrawMenu();
        CFont::DrawFonts();
        return;
    }
    if (g_mode == 0) return;
    char buf[160];
    if (g_mode == 1) {
        RwTexture* t = CurTex();
        sprintf(buf, "BodyTex 1 | %s (%d/%d) | type PRS for menu", t ? t->name : "-", g_idx + 1, (int)g_tex.size());
    } else {
        sprintf(buf, "BodyTex 2 | %s | type PRS for menu", DESIGN_NAME[g_design]);
    }
    Text(20.0f, SH() * 0.85f, buf, C_GOLD_LT, 0.9f);
    CFont::DrawFonts();
}

static void Shutdown() {
    Release();
    CloseSlot();
}

static void LogGameVer() {
    __try {
        Log("game id: 82457C=%04X 8245BC=%02X", (unsigned)*(unsigned short*)0x82457C, (unsigned)*(unsigned char*)0x8245BC);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        Log("game id: unreadable");
    }
}

class BodyTexPlugin {
public:
    BodyTexPlugin() {
        Log("---- BodyTex v0.4 loaded ----");
        LogGameVer();
        Events::gameProcessEvent += Process;
        Events::drawHudEvent += DrawHud;
        Events::shutdownRwEvent += Shutdown;
    }
} bodyTexPlugin;
