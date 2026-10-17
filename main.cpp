// BodyTex.asi v0.1 - GTA San Andreas (1.0 US) - plugin-sdk
// Category 1: apply any in-game texture to car BODY materials only
// Category 2: code-only animated paint jobs (no images)
// F9 opens the mouse menu (camera frozen, free cursor, RGB-border UI).
// Shortcuts with menu closed: Num6/Num4 next/prev | Num9/Num3 +-100 (cat 1) | Num0 off
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
};
static std::vector<MatRec> g_recs;
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
    "light", "lamp", "plate", "interior", "steer", "dummy", "shadow", "wiper", nullptr};
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
    const RwRGBA* col = RpMaterialGetColor(m);
    if (!col || col->alpha < 255) return m;
    RwTexture* t = RpMaterialGetTexture(m);
    const char* tn = t ? t->name : "";
    bool marker = IsMarker(col);
    bool take = false;
    if (marker) take = !c->frameExcl;
    else if (t) take = c->frameBody && !c->frameExcl && !HasAny(tn, TEX_EXCL);
    if (take && !c->hasUV) {
        Log("  skip (no UV): frame=%s tex=%s", c->frame, tn);
        return m;
    }
    Log("  material frame=%s tex=%s marker=%d -> %s", c->frame, tn, marker ? 1 : 0, take ? "BODY" : "skip");
    if (!take) return m;
    for (auto& r : g_recs) if (r.mat == m) return m;  // shared between atomics
    MatRec r;
    r.mat = m;
    r.origTex = t;
    if (t) t->refCount++;  // keep original alive
    const RwSurfaceProperties* sp = RpMaterialGetSurfaceProperties(m);
    if (sp) r.origProps = *sp; else { r.origProps.ambient = 1.0f; r.origProps.specular = 0.0f; r.origProps.diffuse = 1.0f; }
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

static bool Step(int dir) {
    if (!CTxdStore::ms_pTxdPool) return false;
    g_nSlots = CTxdStore::ms_pTxdPool->m_nSize;
    int opens = 0;
    while (opens <= g_nSlots + 2) {
        int ni = g_idx + dir;
        if (g_slot >= 0 && g_opened && ni >= 0 && ni < (int)g_tex.size()) { g_idx = ni; return true; }
        int s = g_slot < 0 ? (dir > 0 ? -1 : g_nSlots) : g_slot;
        do { s += dir; } while (s >= 0 && s < g_nSlots && !SlotValid(s));
        if (s < 0 || s >= g_nSlots) s = dir > 0 ? FirstValid() : LastValid();
        if (s < 0) return false;
        OpenSlot(s);
        opens++;
        g_idx = dir > 0 ? -1 : (int)g_tex.size();
    }
    return false;
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
static const int N_DESIGNS = 9;
static const char* DESIGN_NAME[N_DESIGNS] = {"Rainbow wave", "Fire", "Plasma", "Matrix", "Shapes & symbols",
    "Neon lines (glow)", "Lightning (glow)", "Pulse rings (glow)", "Energy streaks (glow)"};
static const int FIRST_GLOW = 5;

static float Hh(int a, int b = 0, int c = 0) {
    unsigned x = (unsigned)a * 374761393u + (unsigned)b * 668265263u + (unsigned)c * 2147483647u;
    x = (x ^ (x >> 13)) * 1274126177u;
    x ^= x >> 16;
    return (x & 0xFFFF) / 65535.0f;
}
static inline float Cl(float v) { return v < 0 ? 0 : (v > 1 ? 1 : v); }
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
        RpMaterialSetTexture(r.mat, tex);
        if (glow) RpMaterialSetSurfaceProperties(r.mat, &glowProps);
        else RpMaterialSetSurfaceProperties(r.mat, &r.origProps);
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
    Log("body materials found: %d", (int)g_recs.size());
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

// ---------------- menu state ----------------
static bool g_menu = false;
static float g_cx = 0, g_cy = 0;           // virtual cursor (screen px)
static bool g_lmbPrev = true, g_click = false;
static char g_txd[32] = "";
static bool g_focus = false;
static char g_status[96] = "";
static unsigned g_statusT = 0;
static const float MOUSE_SENS = 1.0f;      // tune if cursor feels too slow/fast

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
    if (m == 1 && !CurTex()) Step(1);
    ApplyAll();
}
static void Nav(int n) {
    int d = n > 0 ? 1 : -1;
    for (int i = 0; i < abs(n); i++) if (!Step(d)) break;
    ApplyAll();
}
static void GoTxd() {
    if (!g_txd[0]) { Status("type a TXD name first"); return; }
    if (!CTxdStore::ms_pTxdPool) return;
    g_nSlots = CTxdStore::ms_pTxdPool->m_nSize;
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
    g_cx += MX(m) * MOUSE_SENS;
    g_cy += MY(m) * MOUSE_SENS;
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
static void FillRect(float x, float y, float w, float h, CRGBA c) {
    CSprite2d::DrawRect(CRect(x, y + h, x + w, y), c);
}
static void Text(float x, float y, const char* s, CRGBA col, float scale = 1.0f) {
    char buf[200];
    strncpy(buf, s, sizeof(buf) - 1); buf[sizeof(buf) - 1] = 0;
    CFont::SetFontStyle(FONT_SUBTITLES);
    CFont::SetScale(0.36f * scale * SW() / 640.0f, 0.78f * scale * SH() / 448.0f);
    CFont::SetColor(col);
    CFont::SetOrientation(ALIGN_LEFT);
    CFont::SetEdge(1);
    CFont::SetWrapx(SW());
    CFont::PrintString(x, y, buf);
}
// rotating RGB border: a rainbow that travels around the perimeter
static void RgbBorder(float x, float y, float w, float h, float th) {
    float t = CTimer::m_snTimeInMilliseconds / 1000.0f;
    float L = 2 * (w + h);
    int n = (int)(L / 6.0f); if (n < 16) n = 16;
    float seg = L / n;
    for (int i = 0; i < n; i++) {
        float p = i * seg, r, g, b;
        Hsv(p / L - t * 0.5f, 1.0f, 1.0f, r, g, b);
        CRGBA c((unsigned char)(r * 255), (unsigned char)(g * 255), (unsigned char)(b * 255), 255);
        float sx, sy, sw, sh;
        if (p < w)                  { sx = x + p;                 sy = y;                       sw = seg + 0.6f; sh = th; }
        else if (p < w + h)         { sx = x + w - th;            sy = y + (p - w);             sw = th;         sh = seg + 0.6f; }
        else if (p < 2 * w + h)     { sx = x + w - (p - w - h) - seg; sy = y + h - th;          sw = seg + 0.6f; sh = th; }
        else                        { sx = x;                     sy = y + h - (p - 2 * w - h) - seg; sw = th;     sh = seg + 0.6f; }
        FillRect(sx, sy, sw, sh, c);
    }
}
static bool Hover(float x, float y, float w, float h) {
    return g_cx >= x && g_cx <= x + w && g_cy >= y && g_cy <= y + h;
}
static bool Button(const char* label, float x, float y, float w, float h, bool selected) {
    bool hov = Hover(x, y, w, h);
    CRGBA bg = selected ? CRGBA(35, 85, 165, 235) : (hov ? CRGBA(70, 70, 95, 235) : CRGBA(18, 18, 28, 225));
    FillRect(x, y, w, h, bg);
    RgbBorder(x, y, w, h, selected ? 2.6f : 1.6f);
    Text(x + 8, y + h * 0.18f, label, CRGBA(255, 255, 255, 255), 0.85f);
    return hov && g_click;
}

static void DrawMenu() {
    float W = SW(), H = SH();
    float pw = W * 0.48f, ph = H * 0.66f, px = (W - pw) * 0.5f, py = (H - ph) * 0.5f;
    float pad = 14.0f, gap = 8.0f, bh = H * 0.058f;
    FillRect(px, py, pw, ph, CRGBA(6, 6, 14, 228));
    RgbBorder(px, py, pw, ph, 3.2f);
    Text(px + pad, py + 8, "BodyTex  -  car body painter", CRGBA(255, 255, 255, 255), 1.1f);

    float y = py + H * 0.07f;
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
        sprintf(info, "TXD slot %d | %s (%d/%d)", g_slot, t ? t->name : "-", g_idx + 1, (int)g_tex.size());
        Text(px + pad, y, info, CRGBA(200, 230, 255, 255), 0.9f);
        y += H * 0.05f;
        float bw4 = (pw - 2 * pad - 3 * gap) / 4;
        if (Button("<< 100", px + pad, y, bw4, bh, false)) Nav(-100);
        if (Button("< Prev", px + pad + (bw4 + gap), y, bw4, bh, false)) Nav(-1);
        if (Button("Next >", px + pad + 2 * (bw4 + gap), y, bw4, bh, false)) Nav(1);
        if (Button("100 >>", px + pad + 3 * (bw4 + gap), y, bw4, bh, false)) Nav(100);
        y += bh + H * 0.035f;
        Text(px + pad, y, "Type a TXD name, then click Go (or press Enter):", CRGBA(200, 230, 255, 255), 0.85f);
        y += H * 0.045f;
        inHover = Hover(px + pad, y, inW, bh);
        if (inHover && g_click) g_focus = true;
        FillRect(px + pad, y, inW, bh, CRGBA(0, 0, 0, 235));
        RgbBorder(px + pad, y, inW, bh, g_focus ? 3.0f : 1.4f);
        char shown[48];
        bool blink = ((CTimer::m_snTimeInMilliseconds / 500) & 1) != 0;
        sprintf(shown, "%s%s", g_txd, (g_focus && blink) ? "_" : "");
        Text(px + pad + 8, y + bh * 0.18f, shown, CRGBA(255, 255, 255, 255), 0.9f);
        if (Button("Go", px + pad + inW + gap, y, pw - 2 * pad - inW - gap, bh, false)) GoTxd();
    } else if (g_mode == 2) {
        Text(px + pad, y, "Pick a design (no images, pure code):", CRGBA(200, 230, 255, 255), 0.9f);
        y += H * 0.05f;
        for (int i = 0; i < N_DESIGNS; i++) {
            int cx = i % 3, cy = i / 3;
            if (Button(DESIGN_NAME[i], px + pad + cx * (bw3 + gap), y + cy * (bh + gap), bw3, bh, g_design == i)) {
                g_design = i;
                ApplyAll();
            }
        }
    } else {
        Text(px + pad, y, "Choose a category above. Get into a car to see the result.", CRGBA(200, 230, 255, 255), 0.85f);
    }
    if (g_click && !inHover) g_focus = false;

    // status line + close
    unsigned now = CTimer::m_snTimeInMilliseconds;
    if (g_status[0] && now - g_statusT < 6000)
        Text(px + pad, py + ph - bh - pad - H * 0.04f, g_status, CRGBA(255, 220, 120, 255), 0.85f);
    else if (!g_veh && g_mode != 0)
        Text(px + pad, py + ph - bh - pad - H * 0.04f, "Get into a car to apply.", CRGBA(255, 220, 120, 255), 0.85f);
    if (Button("Close  (F9)", px + pw - pad - bw3, py + ph - bh - pad, bw3, bh, false)) ToggleMenu();

    // cursor: small cross with its own RGB border
    FillRect(g_cx - 1, g_cy - 9, 2, 18, CRGBA(255, 255, 255, 255));
    FillRect(g_cx - 9, g_cy - 1, 18, 2, CRGBA(255, 255, 255, 255));
    RgbBorder(g_cx - 6, g_cy - 6, 12, 12, 1.5f);
    g_click = false;
}

static void Process() {
    CVehicle* v = FindPlayerVehicle(-1, false);
    if (Pressed(VK_F9)) ToggleMenu();
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
    if (v != g_veh) {
        Release();
        if (v) Acquire(v);
        return;
    }
    if (!g_veh) return;
    if (g_mode == 2) {
        if (++g_frame % DYN_EVERY == 0) UpdateDyn();
        if (g_design >= FIRST_GLOW) {
            float t = CTimer::m_snTimeInMilliseconds / 1000.0f, r, g, b;
            Hsv(t * 0.2f, 1, 1, r, g, b);
            CVector p = g_veh->GetPosition();
            CPointLights::AddLight(0, p, CVector(0, 0, 0), 8.0f, r, g, b, 0, false, nullptr);
        }
    }
}

static void DrawHud() {
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
        sprintf(buf, "BodyTex 1 | %s (%d/%d) | F9 menu", t ? t->name : "-", g_idx + 1, (int)g_tex.size());
    } else {
        sprintf(buf, "BodyTex 2 | %s | F9 menu", DESIGN_NAME[g_design]);
    }
    Text(20.0f, SH() * 0.85f, buf, CRGBA(255, 255, 255, 255), 0.9f);
    CFont::DrawFonts();
}

static void Shutdown() {
    Release();
    CloseSlot();
}

class BodyTexPlugin {
public:
    BodyTexPlugin() {
        Log("---- BodyTex v0.2 loaded ----");
        Events::gameProcessEvent += Process;
        Events::drawHudEvent += DrawHud;
        Events::shutdownRwEvent += Shutdown;
    }
} bodyTexPlugin;
