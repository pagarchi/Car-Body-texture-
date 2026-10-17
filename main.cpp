// BodyTex.asi v0.7 - GTA San Andreas (1.0 US) - plugin-sdk
// NEW in v0.7: Animated tab reorganised into categories (Matrix / Neon / Fire-Ice / Space / Water / Gold / Party / Scenes)
//   with a live animated preview. 10 real Matrix designs (tiny letters + sentences, 5 mono + 5 colourful),
//   fixed "Pulse rings" (went black after a few seconds), 14 new detailed scenes (horse, unicorn, skull, ocean,
//   waterfall, dragon eye, galaxy, lava cracks, koi pond, storm, black hole, jellyfish, peacock, dragon scales).
//   Design ids are unchanged, so old saves still load.
// NEW in v0.6: "Save +" tab. Saves the car id + every part texture (game textures and animated designs, mixed)
//   under a name you type (BodyTex_saves.txt). Load = "Spawn" (creates the car with the save) or
//   "Apply" (puts it on the car you sit in; only enabled in a car; wrong car id -> error bar from the bottom).
// Menu: black / gold / RGB theme, "texture menu create by : Parsa Rsi" header (Watch Dogs 2 glitch name)
// Category 1: any in-game texture on the car. Catalog with categories (vehicles / peds / weapons / LS / SF / LV /
//             country / props / interiors / other) + search by TXD name or texture name, paged, no freezes.
// Category 2: code-only animated paint jobs (no images); several different designs can run at once.
// Every part of the car has its own texture: pick one, press "Apply to all parts" (all active parts) or "Set" on a
// single part. Changing one part never changes the others. Auto body detection is unchanged.
// Typing PRS opens the mouse menu (camera frozen, free cursor, RGB-border UI).
// Shortcuts with menu closed: Num6/Num4 next/prev texture (design) | Num9/Num3 next/prev TXD (cat 1) | Num0 off
//   (these paint all active parts)
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
#if __has_include("CCheat.h")
#include "CCheat.h"
#define BT_HAVE_CCHEAT 1
#endif
#include <vector>
#include <string>
#include <cmath>
#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <cstdint>
#include <cctype>
#include <atomic>
#include <algorithm>
#include <unordered_map>
#include <process.h>

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
    int asgKind;      // texture of this part: 0 none (original), 1 game texture, 2 animated design
    RwTexture* asgTex;// kind 1: the texture (we hold a reference)
    int asgSlot;      // kind 1: TXD slot we hold a reference on
    bool asgOwn;      // kind 1: that TXD was streamed in by us
    int asgDesign;    // kind 2: design index
    char asgTxd[24];  // kind 1: name of the TXD the texture came from (needed by the saves)
};
static std::vector<MatRec> g_recs;
static int g_partPage = 0;   // page of the parts list in the menu
static CVehicle* g_veh = nullptr;
static int g_vehModel = -1;
static unsigned char g_origCols[4] = {0, 0, 0, 0};
static int g_mode = 0;  // 0 off, 1 category 1, 2 category 2
static char g_loadedName[32] = "";   // name of the save that was loaded last (for the HUD)

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
    r.asgSlot = -1;
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
// The catalog is built from the game's own files (data\gta.dat -> IDE files, models\*.img) by a background
// thread, so the game never freezes. IDE sections give the category (vehicle / ped / weapon / city / ...),
// the IMG archives give every TXD name, and the TXD headers give the texture names inside each TXD.
static void Status(const char* fmt, ...);
static void ShowError(const char* fmt, ...);
static void ApplySelToAll();

enum { TC_ALL = 0, TC_VEH, TC_PED, TC_WEAP, TC_LS, TC_SF, TC_LV, TC_CNT, TC_PROP, TC_INT, TC_OTHER, N_TC };
static const char* const TC_NAME[N_TC] = {"All", "Vehicles", "Peds", "Weapons", "LS", "SF", "LV",
    "Country", "Props", "Interior", "Other"};
static const char* const TC_FULL[N_TC] = {"All categories", "Vehicles", "Peds", "Weapons", "Los Santos",
    "San Fierro", "Las Venturas", "Countryside", "Props / generic", "Interiors", "Other"};
static const int TC_RANK[N_TC] = {0, 5, 5, 5, 4, 4, 4, 4, 2, 3, 1};

struct TxdEnt { char name[24]; unsigned char cat; int slot; };   // slot: -2 not matched yet, -1 not in this game
struct TexEnt { char name[32]; int txd; };
static std::vector<TxdEnt> g_txds;      // written by the scan thread before g_stage becomes 1
static std::vector<TexEnt> g_texs;      // written by the scan thread before g_stage becomes 2
static std::vector<int> g_txdFirst, g_txdCount;
static std::atomic<int> g_stage(0);     // 0 not started, 1 TXD list ready, 2 texture names ready
static std::atomic<int> g_scanDone(0), g_scanTotal(0);
static std::atomic<bool> g_abort(false);
static HANDLE g_scanThread = nullptr;
static bool g_scanStarted = false;

// ---- scan thread (files only, never touches game structures) ----
struct TmpTxd { char name[24]; unsigned char cat; int img; unsigned long long off; unsigned size; bool hasJob; };
struct Builder {
    std::vector<TmpTxd> v;
    std::unordered_map<std::string, int> idx;
    void Add(const char* nm, int cat, bool upgrade, int img, unsigned long long off, unsigned size) {
        char low[24]; int n = 0;
        for (; nm[n] && n < 23; n++) low[n] = (char)tolower((unsigned char)nm[n]);
        low[n] = 0;
        if (!n) return;
        int i;
        auto it = idx.find(low);
        if (it == idx.end()) {
            TmpTxd t; memset(&t, 0, sizeof(t));
            memcpy(t.name, low, n + 1);
            t.cat = (unsigned char)cat; t.img = -1;
            i = (int)v.size();
            v.push_back(t);
            idx[low] = i;
        } else {
            i = it->second;
            if (upgrade && TC_RANK[cat] > TC_RANK[v[i].cat]) v[i].cat = (unsigned char)cat;
        }
        if (img >= 0 && !v[i].hasJob) { v[i].img = img; v[i].off = off; v[i].size = size; v[i].hasJob = true; }
    }
};
static void TrimInPlace(char* s) {
    char* a = s;
    while (*a == ' ' || *a == '\t' || *a == '\r' || *a == '\n') a++;
    if (a != s) memmove(s, a, strlen(a) + 1);
    size_t n = strlen(s);
    while (n > 0 && (s[n - 1] == ' ' || s[n - 1] == '\t' || s[n - 1] == '\r' || s[n - 1] == '\n')) s[--n] = 0;
}
static void NormPath(const char* in, char* out, size_t cap, bool lower) {
    size_t n = 0;
    for (; in[n] && n + 1 < cap; n++) {
        char c = in[n];
        if (c == '/') c = '\\';
        out[n] = lower ? (char)tolower((unsigned char)c) : c;
    }
    out[n] = 0;
}
static int PathCat(const char* lp) {
    if (strstr(lp, "veh_mods") || strstr(lp, "vehicles")) return TC_VEH;
    if (strstr(lp, "\\la\\")) return TC_LS;
    if (strstr(lp, "\\sf\\")) return TC_SF;
    if (strstr(lp, "\\vegas\\")) return TC_LV;
    if (strstr(lp, "\\country\\")) return TC_CNT;
    if (strstr(lp, "\\interior\\")) return TC_INT;
    if (strstr(lp, "\\generic\\") || strstr(lp, "default.ide") || strstr(lp, "leveldes")) return TC_PROP;
    return TC_OTHER;
}
static void ParseIde(Builder& b, const char* path) {
    FILE* f = fopen(path, "r");
    if (!f) return;
    char lp[260];
    NormPath(path, lp, sizeof(lp), true);
    int pathCat = PathCat(lp);
    int sec = 0;   // 0 none, 1 objs-like, 2 cars, 3 peds, 4 weap, 5 skipped section
    char line[512];
    while (fgets(line, sizeof(line), f)) {
        char* h = strchr(line, '#');
        if (h) *h = 0;
        TrimInPlace(line);
        if (!line[0]) continue;
        if (sec == 0) {
            if (!_stricmp(line, "objs") || !_stricmp(line, "tobj") || !_stricmp(line, "hier") || !_stricmp(line, "anim")) sec = 1;
            else if (!_stricmp(line, "cars")) sec = 2;
            else if (!_stricmp(line, "peds")) sec = 3;
            else if (!_stricmp(line, "weap")) sec = 4;
            else sec = 5;
            continue;
        }
        if (!_stricmp(line, "end")) { sec = 0; continue; }
        if (sec == 5) continue;
        char* fld[3] = {nullptr, nullptr, nullptr};
        int nf = 0;
        char* p = line;
        while (nf < 3) {
            fld[nf++] = p;
            char* c = strchr(p, ',');
            if (!c) break;
            *c = 0;
            p = c + 1;
        }
        if (nf < 3) continue;
        TrimInPlace(fld[2]);
        int cat = sec == 2 ? TC_VEH : (sec == 3 ? TC_PED : (sec == 4 ? TC_WEAP : pathCat));
        b.Add(fld[2], cat, true, -1, 0, 0);
    }
    fclose(f);
}
#pragma pack(push, 1)
struct ImgEnt { uint32_t off; uint16_t stream; uint16_t arch; char name[24]; };
#pragma pack(pop)
struct ScanJob { int txd; int img; unsigned long long off; unsigned size; };

// reads the texture names from a TXD stored in an IMG archive (header chunks only, no pixel data)
static void ScanTxd(FILE* f, unsigned long long base, unsigned maxSize, int txd, std::vector<TexEnt>& out) {
    unsigned char h[28];
    if (_fseeki64(f, (long long)base, SEEK_SET) != 0) return;
    if (fread(h, 1, 28, f) != 28) return;
    unsigned t0, sz0, t1, sz1;
    memcpy(&t0, h, 4); memcpy(&sz0, h + 4, 4);
    memcpy(&t1, h + 12, 4); memcpy(&sz1, h + 16, 4);
    if (t0 != 0x16 || t1 != 0x01) return;
    unsigned short num; memcpy(&num, h + 24, 2);
    unsigned long long end = base + 12ull + sz0;
    if (maxSize && end > base + maxSize) end = base + maxSize;
    unsigned long long pos = base + 24ull + sz1;
    for (int i = 0; i < (int)num && i < 2048; i++) {
        if (pos + 96 > end) break;
        unsigned char b[96];
        if (_fseeki64(f, (long long)pos, SEEK_SET) != 0) break;
        if (fread(b, 1, 96, f) != 96) break;
        unsigned ct, cs, st;
        memcpy(&ct, b, 4); memcpy(&cs, b + 4, 4); memcpy(&st, b + 12, 4);
        if (ct != 0x15 || st != 0x01) break;
        TexEnt te; memset(&te, 0, sizeof(te));
        memcpy(te.name, b + 32, 31);
        te.name[31] = 0;
        bool ok = te.name[0] != 0;
        for (int k = 0; te.name[k]; k++) if ((unsigned char)te.name[k] < 32 || (unsigned char)te.name[k] > 126) { ok = false; break; }
        if (!ok) break;
        te.txd = txd;
        out.push_back(te);
        pos += 12ull + cs;
    }
}
static unsigned __stdcall ScanThread(void*) {
    Builder b;
    std::vector<std::string> imgs;
    imgs.push_back("models\\gta3.img");
    imgs.push_back("models\\gta_int.img");
    // 1) gta.dat -> every IDE (categories) and extra IMG archives
    FILE* gd = fopen("data\\gta.dat", "r");
    if (gd) {
        char line[512];
        while (fgets(line, sizeof(line), gd)) {
            char* h = strchr(line, '#');
            if (h) *h = 0;
            TrimInPlace(line);
            if (line[0] == 0) continue;
            char* sp = strpbrk(line, " \t");
            if (!sp) continue;
            *sp = 0;
            char* rest = sp + 1;
            TrimInPlace(rest);
            if (!rest[0]) continue;
            char np[260];
            NormPath(rest, np, sizeof(np), false);
            if (!_stricmp(line, "IDE")) ParseIde(b, np);
            else if (!_stricmp(line, "IMG")) {
                bool have = false;
                for (auto& s : imgs) if (!_stricmp(s.c_str(), np)) have = true;
                if (!have) imgs.push_back(np);
            }
        }
        fclose(gd);
    }
    // 2) IMG directories -> every TXD name (+ where its data is)
    std::vector<FILE*> files(imgs.size(), nullptr);
    for (size_t k = 0; k < imgs.size() && !g_abort; k++) {
        FILE* f = fopen(imgs[k].c_str(), "rb");
        if (!f) continue;
        files[k] = f;
        char lowName[260];
        NormPath(imgs[k].c_str(), lowName, sizeof(lowName), true);
        bool isInt = strstr(lowName, "int") != nullptr;
        char magic[4]; int count = 0;
        if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "VER2", 4) != 0 || fread(&count, 4, 1, f) != 1 || count <= 0 || count > 400000) {
            fclose(f); files[k] = nullptr;
            continue;
        }
        std::vector<ImgEnt> ents((size_t)count);
        size_t got = fread(ents.data(), sizeof(ImgEnt), (size_t)count, f);
        for (size_t e = 0; e < got; e++) {
            char nm[25]; memcpy(nm, ents[e].name, 24); nm[24] = 0;
            size_t n = strlen(nm);
            if (n < 5 || _stricmp(nm + n - 4, ".txd") != 0) continue;
            nm[n - 4] = 0;
            unsigned sectors = ents[e].stream ? ents[e].stream : ents[e].arch;
            b.Add(nm, isInt ? TC_INT : TC_OTHER, false, (int)k, (unsigned long long)ents[e].off * 2048ull, sectors * 2048u);
        }
    }
    // 3) sorted list + jobs, then publish stage 1
    std::sort(b.v.begin(), b.v.end(), [](const TmpTxd& x, const TmpTxd& y) { return strcmp(x.name, y.name) < 0; });
    std::vector<TxdEnt> pub(b.v.size());
    std::vector<ScanJob> jobs;
    for (size_t i = 0; i < b.v.size(); i++) {
        memcpy(pub[i].name, b.v[i].name, 24);
        pub[i].cat = b.v[i].cat;
        pub[i].slot = -2;
        if (b.v[i].hasJob) { ScanJob j; j.txd = (int)i; j.img = b.v[i].img; j.off = b.v[i].off; j.size = b.v[i].size; jobs.push_back(j); }
    }
    size_t nTxd = pub.size();
    g_scanTotal = (int)jobs.size();
    g_txds.swap(pub);
    g_stage.store(1);
    // 4) texture names, in file order so the disk is read mostly sequentially
    std::sort(jobs.begin(), jobs.end(), [](const ScanJob& x, const ScanJob& y) { return x.img != y.img ? x.img < y.img : x.off < y.off; });
    std::vector<TexEnt> texs;
    std::vector<int> first(nTxd, 0), cnt(nTxd, 0);
    for (size_t k = 0; k < jobs.size() && !g_abort; k++) {
        const ScanJob& j = jobs[k];
        FILE* f = (j.img >= 0 && j.img < (int)files.size()) ? files[j.img] : nullptr;
        if (f) {
            size_t before = texs.size();
            ScanTxd(f, j.off, j.size, j.txd, texs);
            first[j.txd] = (int)before;
            cnt[j.txd] = (int)(texs.size() - before);
        }
        g_scanDone = (int)k + 1;
        if ((k & 63) == 63) Sleep(1);
    }
    for (auto f : files) if (f) fclose(f);
    if (!g_abort) {
        Log("catalog: %d TXDs, %d textures", (int)nTxd, (int)texs.size());
        g_texs.swap(texs);
        g_txdFirst.swap(first);
        g_txdCount.swap(cnt);
        g_stage.store(2);
    }
    return 0;
}
static void CatalogStart() {
    if (g_scanStarted) return;
    g_scanStarted = true;
    g_scanThread = (HANDLE)_beginthreadex(nullptr, 0, ScanThread, nullptr, 0, nullptr);
    if (g_scanThread) SetThreadPriority(g_scanThread, THREAD_PRIORITY_BELOW_NORMAL);
    else Log("catalog thread failed");
}

// ---- TXD slots / streaming ----
static int g_nSlots = 0;
static RwTexDictionary* TxdGet(int slot) {
    auto pool = CTxdStore::ms_pTxdPool;
    if (!pool || slot < 0 || slot >= pool->m_nSize || pool->IsFreeSlotAtIndex(slot)) return nullptr;
    TxdDef* d = pool->GetAt(slot);
    return d ? d->m_pRwDictionary : nullptr;
}
static bool SlotValid(int s) {
    return s >= 0 && s < g_nSlots && !CTxdStore::ms_pTxdPool->IsFreeSlotAtIndex(s);
}
static void ReqTxd(int slot) {
    __try { CStreaming::RequestModel(20000 + slot, 2); } __except (EXCEPTION_EXECUTE_HANDLER) {}
}
static void UnreqTxd(int slot) {
    __try { CStreaming::SetModelIsDeletable(20000 + slot); } __except (EXCEPTION_EXECUTE_HANDLER) {}
}
static int FindSlotSafe(const char* name) {
    char buf[32];
    strncpy(buf, name, 31); buf[31] = 0;
    __try { return CTxdStore::FindTxdSlot(buf); } __except (EXCEPTION_EXECUTE_HANDLER) { return -1; }
}
static RwTexture* TexCB(RwTexture* t, void* d) {
    ((std::vector<RwTexture*>*)d)->push_back(t);
    return t;
}
static bool EnumTex(RwTexDictionary* d, std::vector<RwTexture*>* v) {
    __try { RwTexDictionaryForAllTextures(d, TexCB, v); return true; } __except (EXCEPTION_EXECUTE_HANDLER) { return false; }
}

// ---- catalog browsing state ----
static int g_resolveNext = 0;
static bool g_resolved = false;
static bool g_dirty = true;
static int g_cat = 0;
static bool g_texMode = false;       // false: list TXDs, true: list single textures
static char g_search[32] = "";
static char g_tok[4][32];
static int g_nTok = 0;
static std::vector<int> g_list;      // TXD indexes (TXD mode) or texture indexes (texture mode)
static int g_listPage = 0;

// matches the TXD names against this game's TXD pool a few hundred per frame (no hitch)
static void CatalogPump() {
    if (g_stage.load() < 1 || g_resolved) return;
    auto pool = CTxdStore::ms_pTxdPool;
    if (!pool) return;
    g_nSlots = pool->m_nSize;
    int n = (int)g_txds.size();
    int end = g_resolveNext + 300;
    if (end > n) end = n;
    for (; g_resolveNext < end; g_resolveNext++) {
        TxdEnt& e = g_txds[g_resolveNext];
        int s = FindSlotSafe(e.name);
        e.slot = (s >= 0 && SlotValid(s)) ? s : -1;
    }
    if (g_resolveNext >= n) { g_resolved = true; g_dirty = true; }
}
static bool IHas(const char* s, const char* lowSub) {   // case-insensitive substring, lowSub is lower-case
    if (!lowSub[0]) return true;
    for (; *s; s++) {
        const char* a = s; const char* b = lowSub;
        while (*a && *b && (char)tolower((unsigned char)*a) == *b) { a++; b++; }
        if (!*b) return true;
    }
    return false;
}
static void ParseTokens() {
    g_nTok = 0;
    const char* p = g_search;
    while (*p && g_nTok < 4) {
        while (*p == ' ') p++;
        if (!*p) break;
        int n = 0;
        while (*p && *p != ' ' && n < 31) g_tok[g_nTok][n++] = (char)tolower((unsigned char)*p++);
        g_tok[g_nTok][n] = 0;
        g_nTok++;
        while (*p && *p != ' ') p++;
    }
}
static bool TxdHasTexLike(int i, const char* tok) {
    if (g_stage.load() < 2 || i >= (int)g_txdFirst.size()) return false;
    int f = g_txdFirst[i], c = g_txdCount[i];
    for (int k = 0; k < c; k++) if (IHas(g_texs[f + k].name, tok)) return true;
    return false;
}
// a TXD passes when it is in the category and every search word is in its name or in one of its texture names
static bool TxdPass(int i) {
    const TxdEnt& e = g_txds[i];
    if (e.slot < 0) return false;
    if (g_cat != TC_ALL && e.cat != g_cat) return false;
    for (int t = 0; t < g_nTok; t++)
        if (!IHas(e.name, g_tok[t]) && !TxdHasTexLike(i, g_tok[t])) return false;
    return true;
}
static void RebuildList() {
    g_dirty = false;
    g_list.clear();
    g_listPage = 0;
    ParseTokens();
    int stage = g_stage.load();
    if (stage < 1 || !g_resolved) return;
    if (!g_texMode) {
        for (int i = 0; i < (int)g_txds.size(); i++) if (TxdPass(i)) g_list.push_back(i);
    } else if (stage >= 2) {
        for (int j = 0; j < (int)g_texs.size(); j++) {
            const TexEnt& t = g_texs[j];
            const TxdEnt& e = g_txds[t.txd];
            if (e.slot < 0) continue;
            if (g_cat != TC_ALL && e.cat != g_cat) continue;
            bool ok = true;
            for (int k = 0; k < g_nTok; k++)
                if (!IHas(t.name, g_tok[k]) && !IHas(e.name, g_tok[k])) { ok = false; break; }
            if (ok) g_list.push_back(j);
        }
    }
}

// ---- opening one TXD (asynchronous: the streamer loads it, the game never blocks) ----
static int g_slot = -1, g_idx = -1, g_openIdx = -1;
static bool g_opened = false, g_weLoaded = false;
static std::vector<RwTexture*> g_tex;
static int g_pendSlot = -1;
static DWORD g_pendT0 = 0;
static char g_openName[24] = "";
static char g_wantTex[32] = "";
static int g_wantEdge = 0;            // which texture to select after opening: 0 first, -1 last
static bool g_applyAfterOpen = false; // numpad shortcuts: paint the car as soon as the TXD is open
static int g_view = 0;                // 0 = list, 1 = textures of the opened TXD
static int g_texPage = 0;
static bool g_texJump = false;

static RwTexture* CurTex() {
    if (g_opened && g_idx >= 0 && g_idx < (int)g_tex.size()) return g_tex[g_idx];
    return nullptr;
}
static void CloseSlot() {
    if (g_opened && g_slot >= 0) {
        CTxdStore::RemoveRef(g_slot);
        if (g_weLoaded) CStreaming::SetModelIsDeletable(20000 + g_slot);
    }
    g_tex.clear();
    g_opened = false;
}
static void CancelPending() {
    if (g_pendSlot >= 0) {
        if (g_weLoaded) UnreqTxd(g_pendSlot);
        g_pendSlot = -1;
    }
}
static void SelectWanted() {
    int n = (int)g_tex.size();
    g_idx = -1;
    if (n == 0) return;
    if (g_wantTex[0])
        for (int i = 0; i < n; i++) if (_stricmp(g_tex[i]->name, g_wantTex) == 0) { g_idx = i; break; }
    if (g_idx < 0) g_idx = (g_wantEdge < 0) ? n - 1 : 0;
    g_texJump = true;
    if (g_applyAfterOpen) { g_applyAfterOpen = false; ApplySelToAll(); }
}
static void FinishOpen() {
    int s = g_pendSlot;
    g_pendSlot = -1;
    RwTexDictionary* dict = TxdGet(s);
    if (!dict) { Status("TXD '%s' could not be opened", g_openName); return; }
    CTxdStore::AddRef(s);
    g_opened = true;
    g_slot = s;
    g_tex.clear();
    if (!EnumTex(dict, &g_tex)) g_tex.clear();
    if (g_tex.empty()) Status("TXD '%s' has no readable textures", g_openName);
    else Status("TXD '%s' - %d textures", g_openName, (int)g_tex.size());
    SelectWanted();
}
static void PumpOpen() {
    if (g_pendSlot < 0) return;
    if (TxdGet(g_pendSlot)) { FinishOpen(); return; }
    if (GetTickCount() - g_pendT0 > 8000) {
        Status("TXD '%s' did not load, try again", g_openName);
        CancelPending();
    }
}
static void BeginOpen(int slot, int txdIdx, const char* name, const char* wantTex, int edge) {
    if (slot < 0) return;
    g_view = 1;
    g_texPage = 0;
    g_texJump = true;
    g_openIdx = txdIdx;
    strncpy(g_openName, name, 23); g_openName[23] = 0;
    g_wantTex[0] = 0;
    if (wantTex) { strncpy(g_wantTex, wantTex, 31); g_wantTex[31] = 0; }
    g_wantEdge = edge;
    if (g_opened && g_slot == slot && g_pendSlot < 0) { SelectWanted(); return; }
    CancelPending();
    CloseSlot();
    g_slot = slot;
    g_idx = -1;
    g_weLoaded = (TxdGet(slot) == nullptr);
    g_pendSlot = slot;
    g_pendT0 = GetTickCount();
    if (!g_weLoaded) FinishOpen(); else ReqTxd(slot);
}
static void OpenTxdIdx(int i, int edge) {
    BeginOpen(g_txds[i].slot, i, g_txds[i].name, nullptr, edge);
}
// Enter / Go: opens the TXD with exactly this name, otherwise the first search result
static void GoSearch() {
    char nm[32];
    strncpy(nm, g_search, 31); nm[31] = 0;
    TrimInPlace(nm);
    if (!nm[0]) { Status("type a TXD name first"); return; }
    if (!CTxdStore::ms_pTxdPool) return;
    g_nSlots = CTxdStore::ms_pTxdPool->m_nSize;
    int s = FindSlotSafe(nm);
    if (s >= 0 && SlotValid(s)) {
        int ti = -1;
        for (int i = 0; i < (int)g_txds.size(); i++) if (_stricmp(g_txds[i].name, nm) == 0) { ti = i; break; }
        BeginOpen(s, ti, nm, nullptr, 0);
        return;
    }
    if (!g_texMode && !g_list.empty()) { OpenTxdIdx(g_list[0], 0); return; }
    Status("TXD '%s' not found", nm);
}
// next / previous TXD that passes the current category + search filter
static int NextTxd(int dir) {
    int n = (int)g_txds.size();
    if (n == 0 || !g_resolved) return -1;
    if (g_dirty) RebuildList();
    int start = g_openIdx;
    if (start < 0 || start >= n) start = dir > 0 ? -1 : n;
    for (int k = 0; k < n; k++) {
        start += dir;
        if (start >= n) start = 0;
        if (start < 0) start = n - 1;
        if (TxdPass(start)) return start;
    }
    return -1;
}
// numpad shortcuts (menu closed): move and paint the whole car right away
static void QuickTxd(int dir, int edge) {
    CatalogStart();
    int i = NextTxd(dir);
    if (i < 0) { Status("texture list is not ready yet"); return; }
    g_applyAfterOpen = true;
    OpenTxdIdx(i, edge);
}
static void QuickTex(int dir) {
    if (g_pendSlot >= 0) return;
    if (g_opened && !g_tex.empty()) {
        int ni = g_idx + dir;
        if (ni >= 0 && ni < (int)g_tex.size()) { g_idx = ni; ApplySelToAll(); return; }
    }
    QuickTxd(dir, dir > 0 ? 0 : -1);
}

// ---------------- category 2: procedural paint ----------------
// Every design keeps a fixed id (saves store it). The menu groups the ids into categories.
static int g_design = 0;
static int g_frame = 0;
static const int N_DESIGNS = 59;
static const char* DESIGN_NAME[N_DESIGNS] = {
    "Rainbow wave", "Fire", "Plasma", "Matrix: Green rain", "Shapes & symbols",                       // 0-4
    "Neon lines", "Lightning", "Pulse rings", "Energy streaks",                                       // 5-8
    "Aurora", "Neon grid", "Gold shimmer", "Cyber stripes", "Starfield", "Lava", "Ice crystals", "Equalizer",   // 9-16
    "Radar sweep", "Hyperspace", "Police lights", "Rainbow spiral", "Ripples", "Synthwave", "Neon bokeh",       // 17-23
    "Liquid chrome", "Acid plasma", "Nebula", "Gold & black", "Circuit pulses", "Electric waves", "Fire & Ice", // 24-30
    "Disco tiles", "Laser beams", "Caustics", "Hearts pulse", "Golden stars",                                   // 31-35
    "Matrix: Green sentences", "Matrix: Blue text columns", "Matrix: Red binary", "Matrix: Silver flicker",     // 36-39
    "Matrix: Rainbow rain", "Matrix: Rainbow text columns", "Matrix: Multicolor flicker",                       // 40-42
    "Matrix: Rainbow sentences", "Matrix: Neon binary",                                                         // 43-44
    "Galloping horse", "Horse skull on fire", "Unicorn", "Ocean waves", "Waterfall", "Dragon eye",              // 45-50
    "Spiral galaxy", "Molten lava cracks", "Koi pond", "Thunderstorm", "Black hole", "Jellyfish",               // 51-56
    "Peacock feathers", "Dragon scales"                                                                         // 57-58
};
enum { DC_MATRIX = 0, DC_NEON, DC_FIRE, DC_SPACE, DC_WATER, DC_GOLD, DC_PARTY, DC_SCENE, N_DC };
static const unsigned char DCL_MATRIX[] = {3, 36, 37, 38, 39, 40, 41, 42, 43, 44};
static const unsigned char DCL_NEON[]   = {5, 6, 7, 8, 10, 12, 23, 28, 29, 32, 22};
static const unsigned char DCL_FIRE[]   = {1, 14, 15, 30};
static const unsigned char DCL_SPACE[]  = {13, 26, 18, 9};
static const unsigned char DCL_WATER[]  = {21, 33, 24};
static const unsigned char DCL_GOLD[]   = {11, 27, 35};
static const unsigned char DCL_PARTY[]  = {0, 2, 4, 16, 17, 19, 20, 25, 31, 34};
static const unsigned char DCL_SCENE[]  = {45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58};
struct DesignCat { const char* name; const unsigned char* ids; int n; };
static const DesignCat DCATS[N_DC] = {
    {"Matrix",  DCL_MATRIX, (int)sizeof(DCL_MATRIX)},
    {"Neon",    DCL_NEON,   (int)sizeof(DCL_NEON)},
    {"Fire/Ice",DCL_FIRE,   (int)sizeof(DCL_FIRE)},
    {"Space",   DCL_SPACE,  (int)sizeof(DCL_SPACE)},
    {"Water",   DCL_WATER,  (int)sizeof(DCL_WATER)},
    {"Gold",    DCL_GOLD,   (int)sizeof(DCL_GOLD)},
    {"Party",   DCL_PARTY,  (int)sizeof(DCL_PARTY)},
    {"Scenes",  DCL_SCENE,  (int)sizeof(DCL_SCENE)}
};
static int g_designCat = 0;               // category shown in the menu
static int DesignCatOf(int id) {
    for (int c = 0; c < N_DC; c++) for (int i = 0; i < DCATS[c].n; i++) if (DCATS[c].ids[i] == id) return c;
    return 0;
}
// next / previous design in menu order (walks through all categories)
static int DesignStep(int cur, int dir) {
    int c = DesignCatOf(cur), i = 0;
    for (; i < DCATS[c].n; i++) if (DCATS[c].ids[i] == cur) break;
    i += dir;
    while (i < 0) { c = (c + N_DC - 1) % N_DC; i += DCATS[c].n; }
    while (i >= DCATS[c].n) { i -= DCATS[c].n; c = (c + 1) % N_DC; }
    return DCATS[c].ids[i];
}
// every design except the first few plain ones is self-lit (glows); the big scenes too
static bool DesignIsGlow(int d) { return d >= 5 || d == 3; }
static bool DesignIsScene(int d) { return d >= 45; }


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
// ---------------- small math helpers for the big scenes ----------------
static inline float bMix(float a, float b, float t) { return a + (b - a) * t; }
static inline float bMin(float a, float b) { return a < b ? a : b; }
static inline float bMax(float a, float b) { return a > b ? a : b; }
static inline float bSm(float a, float b, float x) { float t = Cl((x - a) / (b - a)); return t * t * (3 - 2 * t); }
static inline float bLen(float x, float y) { return sqrtf(x * x + y * y); }
static float bVn(float x, float y) {
    int ix = (int)floorf(x), iy = (int)floorf(y);
    float fx = x - ix, fy = y - iy;
    fx = fx * fx * (3 - 2 * fx); fy = fy * fy * (3 - 2 * fy);
    float a = Hh(ix, iy, 11), b = Hh(ix + 1, iy, 11), c = Hh(ix, iy + 1, 11), d = Hh(ix + 1, iy + 1, 11);
    return bMix(bMix(a, b, fx), bMix(c, d, fx), fy);
}
static float bFbm(float x, float y) {
    return (0.5f * bVn(x, y) + 0.25f * bVn(x * 2 + 5.3f, y * 2 + 1.7f) + 0.125f * bVn(x * 4 + 9.1f, y * 4 + 3.3f)) / 0.875f;
}
// signed distances (negative inside)
static float bCap(float px, float py, float ax, float ay, float bx, float by, float r) {
    float pax = px - ax, pay = py - ay, bax = bx - ax, bay = by - ay;
    float h = Cl((pax * bax + pay * bay) / (bax * bax + bay * bay + 1e-6f));
    return bLen(pax - bax * h, pay - bay * h) - r;
}
static float bTap(float px, float py, float ax, float ay, float bx, float by, float r0, float r1) {
    float pax = px - ax, pay = py - ay, bax = bx - ax, bay = by - ay;
    float h = Cl((pax * bax + pay * bay) / (bax * bax + bay * bay + 1e-6f));
    return bLen(pax - bax * h, pay - bay * h) - bMix(r0, r1, h);
}
static float bEll(float px, float py, float cx, float cy, float rx, float ry) {
    float x = (px - cx) / rx, y = (py - cy) / ry;
    return (bLen(x, y) - 1.0f) * bMin(rx, ry);
}

// ---------------- Matrix: tiny 5x7 glyphs (digits 0-9, letters A-Z, space) ----------------
static const uint8_t MFONT[37][7] = {
    {0b01110,0b10001,0b10011,0b10101,0b11001,0b10001,0b01110}, // 0
    {0b00100,0b01100,0b00100,0b00100,0b00100,0b00100,0b01110}, // 1
    {0b01110,0b10001,0b00001,0b00010,0b00100,0b01000,0b11111}, // 2
    {0b11110,0b00001,0b00001,0b01110,0b00001,0b00001,0b11110}, // 3
    {0b00010,0b00110,0b01010,0b10010,0b11111,0b00010,0b00010}, // 4
    {0b11111,0b10000,0b11110,0b00001,0b00001,0b10001,0b01110}, // 5
    {0b00110,0b01000,0b10000,0b11110,0b10001,0b10001,0b01110}, // 6
    {0b11111,0b00001,0b00010,0b00100,0b01000,0b01000,0b01000}, // 7
    {0b01110,0b10001,0b10001,0b01110,0b10001,0b10001,0b01110}, // 8
    {0b01110,0b10001,0b10001,0b01111,0b00001,0b00010,0b01100}, // 9
    {0b01110,0b10001,0b10001,0b11111,0b10001,0b10001,0b10001}, // A
    {0b11110,0b10001,0b10001,0b11110,0b10001,0b10001,0b11110}, // B
    {0b01110,0b10001,0b10000,0b10000,0b10000,0b10001,0b01110}, // C
    {0b11110,0b10001,0b10001,0b10001,0b10001,0b10001,0b11110}, // D
    {0b11111,0b10000,0b10000,0b11110,0b10000,0b10000,0b11111}, // E
    {0b11111,0b10000,0b10000,0b11110,0b10000,0b10000,0b10000}, // F
    {0b01110,0b10001,0b10000,0b10111,0b10001,0b10001,0b01111}, // G
    {0b10001,0b10001,0b10001,0b11111,0b10001,0b10001,0b10001}, // H
    {0b01110,0b00100,0b00100,0b00100,0b00100,0b00100,0b01110}, // I
    {0b00111,0b00010,0b00010,0b00010,0b00010,0b10010,0b01100}, // J
    {0b10001,0b10010,0b10100,0b11000,0b10100,0b10010,0b10001}, // K
    {0b10000,0b10000,0b10000,0b10000,0b10000,0b10000,0b11111}, // L
    {0b10001,0b11011,0b10101,0b10101,0b10001,0b10001,0b10001}, // M
    {0b10001,0b10001,0b11001,0b10101,0b10011,0b10001,0b10001}, // N
    {0b01110,0b10001,0b10001,0b10001,0b10001,0b10001,0b01110}, // O
    {0b11110,0b10001,0b10001,0b11110,0b10000,0b10000,0b10000}, // P
    {0b01110,0b10001,0b10001,0b10001,0b10101,0b10010,0b01101}, // Q
    {0b11110,0b10001,0b10001,0b11110,0b10100,0b10010,0b10001}, // R
    {0b01111,0b10000,0b10000,0b01110,0b00001,0b00001,0b11110}, // S
    {0b11111,0b00100,0b00100,0b00100,0b00100,0b00100,0b00100}, // T
    {0b10001,0b10001,0b10001,0b10001,0b10001,0b10001,0b01110}, // U
    {0b10001,0b10001,0b10001,0b10001,0b10001,0b01010,0b00100}, // V
    {0b10001,0b10001,0b10001,0b10101,0b10101,0b10101,0b01010}, // W
    {0b10001,0b10001,0b01010,0b00100,0b01010,0b10001,0b10001}, // X
    {0b10001,0b10001,0b01010,0b00100,0b00100,0b00100,0b00100}, // Y
    {0b11111,0b00001,0b00010,0b00100,0b01000,0b10000,0b11111}, // Z
    {0,0,0,0,0,0,0}                                              // space
};
static const char* const MAT_TEXT[] = {
    "WAKE UP NEO ", "THE MATRIX HAS YOU ", "FOLLOW THE WHITE RABBIT ", "THERE IS NO SPOON ",
    "FREE YOUR MIND ", "WELCOME TO THE REAL WORLD ", "KNOCK KNOCK NEO ", "PARSA RSI TEXTURE MENU ",
    "I KNOW KUNG FU ", "NO ONE CAN BE TOLD WHAT THE MATRIX IS "
};
static const int MAT_NTEXT = 10;
static int MatCharIdx(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'A' && c <= 'Z') return 10 + (c - 'A');
    return 36;
}
static inline bool MatBit(int g, int lx, int ly) {
    if (lx < 0 || lx > 4 || ly < 0 || ly > 6) return false;
    return (MFONT[g][ly] >> (4 - lx)) & 1;
}
// ids of the ten matrix designs: 3 (classic green) and 36..44
static int MatVariant(int d) { return d == 3 ? 0 : ((d >= 36 && d <= 44) ? d - 35 : -1); }
// style: 0 falling random glyphs, 1 falling text columns, 2 sentences scrolling sideways, 3 binary rain, 4 flickering grid
static const int MAT_STYLE[10] = {0, 2, 1, 3, 4,   0, 1, 4, 2, 3};
// every glyph cell is 6x8 px of the 256 px texture: 42 columns x 32 rows of tiny letters
static void MatrixPixel(int var, float u, float v, float t, float& r, float& g, float& b) {
    const int CW = 6, CH = 8, COLS = 42, ROWS = 32;
    int ix = (int)(u * DYN_SIZE), iy = (int)(v * DYN_SIZE);
    int cx = ix / CW, cy = iy / CH;
    if (cx >= COLS || cy >= ROWS) { r = g = b = 0; return; }
    int lx = ix - cx * CW, ly = iy - cy * CH;
    int style = MAT_STYLE[var];
    float br = 0; int gl = 36;
    const float TR = 14.0f;
    if (style == 0 || style == 3 || style == 1) {
        for (int s = 0; s < 2; s++) {
            float sp = 0.25f + 0.5f * Hh(cx, 1 + s * 20);
            float head = Fr(t * sp * 0.45f + Hh(cx, 7 + s * 20)) * (ROWS + TR);
            float d = head - cy;
            if (d < 0 || d >= TR) continue;
            float k = powf(1.0f - d / TR, 1.5f);
            if (k > br) {
                br = k;
                if (style == 1) gl = -1;   // chosen below
                else if (style == 3) gl = Hh(cx, cy, (int)(t * (d < 1 ? 14 : 3) + Hh(cx, cy, 5) * 6) + s) > 0.5f ? 1 : 0;
                else gl = (int)(Hh(cx, cy, (int)(t * (d < 1 ? 14 : 2.5f) + Hh(cx, cy, 5) * 6) + s) * 36.0f) % 36;
                if (d < 1.0f) br = 1.25f;
            }
        }
        if (style == 1) {
            int si = (int)(Hh(cx, 2) * MAT_NTEXT) % MAT_NTEXT;
            const char* tx = MAT_TEXT[si]; int len = (int)strlen(tx);
            gl = MatCharIdx(tx[(cy + (int)(Hh(cx, 3) * 50)) % len]);
            br = bMax(br, 0.22f);          // the text stays faintly visible, the falling light reveals it
        }
    } else if (style == 2) {
        if (cy & 1) { r = g = b = 0; return; }
        int line = cy >> 1;
        int si = (int)(Hh(line, 4) * MAT_NTEXT) % MAT_NTEXT;
        const char* tx = MAT_TEXT[si]; int len = (int)strlen(tx);
        float sp = 2.0f + 3.0f * Hh(line, 5);
        int off = (int)floorf(t * sp) * ((line & 1) ? 1 : -1);
        gl = MatCharIdx(tx[(((cx + off + (int)(Hh(line, 6) * 40)) % len) + len) % len]);
        br = 0.3f + 0.7f * (0.5f + 0.5f * sinf(cx * 0.22f - t * 2.2f + line * 0.9f));
    } else {
        float ph = Hh(cx, cy, 9);
        gl = (int)(Hh(cx, cy, (int)(t * 1.6f + ph * 5.0f)) * 36.0f) % 36;
        float w = 0.5f + 0.5f * sinf(t * 1.3f + cx * 0.33f + cy * 0.21f + ph * 6.0f);
        br = 0.12f + 0.88f * bSm(0.45f, 1.0f, w);
        if (Hh(cx, cy, (int)(t * 6.0f)) > 0.97f) br = 1.2f;
    }
    if (br <= 0 || !MatBit(gl, lx, ly)) { r = g = b = 0; return; }
    float cr, cg, cb;
    switch (var) {
        case 0: cr = 0.10f; cg = 1.00f; cb = 0.25f; break;
        case 1: cr = 0.15f; cg = 1.00f; cb = 0.30f; break;
        case 2: cr = 0.20f; cg = 0.60f; cb = 1.00f; break;
        case 3: cr = 1.00f; cg = 0.08f; cb = 0.08f; break;
        case 4: cr = 0.85f; cg = 0.90f; cb = 1.00f; break;
        case 5: Hsv(Hh(cx, 11) + t * 0.05f, 1.0f, 1.0f, cr, cg, cb); break;
        case 6: Hsv(cx / (float)COLS + t * 0.15f, 1.0f, 1.0f, cr, cg, cb); break;
        case 7: Hsv(Hh(cx, cy, 13) + t * 0.08f, 1.0f, 1.0f, cr, cg, cb); break;
        case 8: Hsv((cy >> 1) / 16.0f + t * 0.12f, 1.0f, 1.0f, cr, cg, cb); break;
        default: if (Hh(cx, 12) > 0.5f) { cr = 1.0f; cg = 0.1f; cb = 0.9f; } else { cr = 0.1f; cg = 0.9f; cb = 1.0f; } break;
    }
    float hi = Cl((br - 0.85f) * 2.5f) * 0.7f;       // bright head of each stream turns whitish
    float k = bMin(br, 1.0f);
    r = cr * k + hi; g = cg * k + hi; b = cb * k + hi;
}

// ---------------- big animated scenes (ids 45..58); drawn at half resolution (128x128) to stay fast ----------------
struct HorseD { float body, mane, tail; };
// horse facing +x, y down, body length about 1.9. ph = gait phase
static HorseD HorseSdf(float x, float y, float ph) {
    HorseD h; h.mane = h.tail = 9.0f;
    y -= 0.03f * sinf(2.0f * ph);
    float d = bEll(x, y, 0.0f, 0.0f, 0.50f, 0.20f);
    d = bMin(d, bEll(x, y, 0.30f, -0.02f, 0.24f, 0.22f));
    d = bMin(d, bEll(x, y, -0.36f, -0.01f, 0.22f, 0.21f));
    d = bMin(d, bTap(x, y, 0.40f, -0.10f, 0.60f, -0.40f, 0.13f, 0.085f));
    d = bMin(d, bTap(x, y, 0.60f, -0.40f, 0.86f, -0.31f, 0.08f, 0.05f));
    d = bMin(d, bCap(x, y, 0.60f, -0.47f, 0.63f, -0.56f, 0.02f));
    static const float LA[4][3] = {{0.34f, 0.14f, 0.0f}, {0.30f, 0.14f, 0.45f}, {-0.40f, 0.14f, 2.7f}, {-0.34f, 0.14f, 3.15f}};
    for (int i = 0; i < 4; i++) {
        float s = ph + LA[i][2];
        float th1 = 0.75f * sinf(s);
        float kx = LA[i][0] + 0.26f * sinf(th1), ky = LA[i][1] + 0.26f * cosf(th1);
        float th2 = th1 - 1.0f * bMax(0.0f, cosf(s));
        float fx = kx + 0.28f * sinf(th2), fy = ky + 0.28f * cosf(th2);
        d = bMin(d, bTap(x, y, LA[i][0], LA[i][1], kx, ky, 0.075f, 0.045f));
        d = bMin(d, bTap(x, y, kx, ky, fx, fy, 0.04f, 0.028f));
    }
    h.body = d;
    float m = 9.0f;
    for (int k = 0; k < 3; k++) {
        float ax = 0.60f - 0.10f * k, ay = -0.42f + 0.10f * k;
        float bx = ax - 0.16f - 0.04f * sinf(ph + k * 1.3f), by = ay - 0.02f + 0.05f * cosf(ph + k);
        m = bMin(m, bTap(x, y, ax, ay, bx, by, 0.035f, 0.01f));
    }
    h.mane = m;
    float p1x = -0.75f, p1y = -0.02f + 0.05f * sinf(ph), p2x = -0.95f, p2y = 0.10f + 0.09f * sinf(ph - 0.8f);
    h.tail = bMin(bTap(x, y, -0.55f, -0.05f, p1x, p1y, 0.04f, 0.05f), bTap(x, y, p1x, p1y, p2x, p2y, 0.05f, 0.015f));
    return h;
}
static inline void bPut(float& r, float& g, float& b, float cr, float cg, float cb, float a) {
    r = bMix(r, cr, a); g = bMix(g, cg, a); b = bMix(b, cb, a);
}
static inline float bEdge(float d) { return bSm(0.012f, -0.012f, d); }   // 1 inside, 0 outside, soft border

static void SceneHorse(float x, float y, float t, float& r, float& g, float& b) {
    // sunset sky, sun, scrolling mountains and ground
    float sk = Cl((y + 1.0f) / 1.6f);
    r = bMix(0.12f, 1.0f, sk * sk); g = bMix(0.05f, 0.42f, sk * sk); b = bMix(0.30f, 0.18f, sk);
    float sd = bLen(x - 0.25f, y + 0.15f);
    bPut(r, g, b, 1.0f, 0.85f, 0.45f, bSm(0.30f, 0.27f, sd)); r += 0.4f * expf(-sd * sd * 6.0f); g += 0.2f * expf(-sd * sd * 6.0f);
    float sx = x + t * 0.35f;
    float ridge = 0.22f + 0.10f * sinf(sx * 3.0f) + 0.05f * sinf(sx * 7.3f + 1.0f);
    if (y > ridge) bPut(r, g, b, 0.22f, 0.08f, 0.22f, 1.0f);
    float ridge2 = 0.42f + 0.06f * sinf((x + t * 0.9f) * 4.0f) + 0.03f * sinf((x + t * 0.9f) * 11.0f);
    if (y > ridge2) bPut(r, g, b, 0.10f, 0.03f, 0.10f, 1.0f);
    if (y > 0.62f) {
        float gr = Hh((int)((x + t * 2.6f) * 45), (int)(y * 45));
        bPut(r, g, b, 0.05f + 0.10f * gr, 0.03f + 0.05f * gr, 0.03f, 1.0f);
        float dust = bFbm((x + t * 2.0f) * 5.0f, y * 8.0f) * bSm(0.62f, 0.8f, y) * bSm(1.0f, 0.2f, x + 0.9f) ;
        bPut(r, g, b, 0.9f, 0.5f, 0.3f, dust * 0.3f);
    }
    float hx = x * 1.15f, hy = (y - 0.05f) * 1.15f;
    if (fabsf(hx) < 1.2f && hy > -0.8f && hy < 0.7f) {
        HorseD h = HorseSdf(hx, hy, t * 9.0f);
        float dd = bMin(h.body, bMin(h.mane, h.tail));
        float inside = bEdge(dd);
        float rim = expf(bMin(dd, 0.0f) * 70.0f);
        float cr = 0.05f + 0.9f * rim, cg = 0.025f + 0.4f * rim, cb = 0.02f + 0.12f * rim;
        bPut(r, g, b, cr, cg, cb, inside);
    }
}
static void SceneUnicorn(float x, float y, float t, float& r, float& g, float& b) {
    float sk = Cl((y + 1.0f) * 0.5f);
    Hsv(0.78f - 0.25f * sk + 0.03f * sinf(t * 0.5f), 0.35f, 0.95f, r, g, b);
    float cl = bFbm(x * 2.2f + t * 0.12f, y * 3.0f + 3.0f);
    bPut(r, g, b, 1.0f, 0.95f, 1.0f, bSm(0.52f, 0.75f, cl) * 0.8f);
    int cx = (int)floorf((x + 1.0f) * 12.0f), cy = (int)floorf((y + 1.0f) * 12.0f);
    float hh = Hh(cx, cy, 4);
    if (hh > 0.8f) {
        float fx = (x + 1.0f) * 12.0f - cx - 0.5f, fy = (y + 1.0f) * 12.0f - cy - 0.5f;
        float tw = 0.5f + 0.5f * sinf(t * 4.0f + hh * 40.0f);
        float st = expf(-fabsf(fx) * 18.0f - fabsf(fy) * 2.5f) + expf(-fabsf(fy) * 18.0f - fabsf(fx) * 2.5f);
        bPut(r, g, b, 1, 1, 1, bMin(1.0f, st * tw));
    }
    float hx = x * 1.05f, hy = (y - 0.12f) * 1.05f;
    float ph = t * 6.5f;
    if (fabsf(hx) < 1.1f && hy > -0.85f && hy < 0.6f) {
        HorseD h = HorseSdf(hx, hy, ph);
        float hr, hg, hb; Hsv(Fr(hx * 1.3f - t * 0.5f + hy * 0.8f), 0.85f, 1.0f, hr, hg, hb);
        float mt = bMin(h.mane, h.tail);
        bPut(r, g, b, hr, hg, hb, bEdge(mt));
        bPut(r, g, b, 0.50f, 0.30f, 0.75f, bEdge(h.body - 0.014f));
        float sh = 0.82f + 0.18f * Cl(-h.body * 10.0f);
        bPut(r, g, b, 1.0f * sh, 0.97f * sh, 1.0f * sh, bEdge(h.body));
        bPut(r, g, b, 0.8f, 0.75f, 0.95f, bEdge(h.body) * expf(h.body * 120.0f) * 0.5f);
        // horn
        float ax = 0.74f, ay = -0.37f, bx = 0.94f, by = -0.70f;
        float pax = hx - ax, pay = hy - ay, bax = bx - ax, bay = by - ay;
        float hp = Cl((pax * bax + pay * bay) / (bax * bax + bay * bay));
        float hd = bLen(pax - bax * hp, pay - bay * hp) - bMix(0.04f, 0.004f, hp);
        float stripe = 0.5f + 0.5f * sinf(hp * 40.0f - t * 4.0f);
        bPut(r, g, b, bMix(1.0f, 1.0f, stripe), bMix(0.8f, 1.0f, stripe), bMix(0.3f, 0.8f, stripe), bEdge(hd));
        float hg2 = bLen(hx - bx, hy - by);
        float sp = 0.6f + 0.4f * sinf(t * 7.0f);
        r += sp * expf(-hg2 * hg2 * 90.0f); g += sp * expf(-hg2 * hg2 * 90.0f); b += sp * expf(-hg2 * hg2 * 90.0f);
    }
}
static void SceneHorseSkull(float x, float y, float t, float& r, float& g, float& b) {
    // fire behind the skull
    float n = bFbm(x * 2.5f, y * 2.5f + t * 1.6f);
    float f = Cl(n * 1.7f - 0.25f + 0.55f * y - 0.35f * bLen(x * 0.7f, y * 0.4f - 0.2f));
    f *= 0.8f; r = Cl(f * 2.2f); g = Cl(f * 1.5f - 0.45f); b = Cl(f * 0.6f - 0.4f) * 0.4f;
    r += 0.04f; g += 0.0f; b += 0.03f;
    float hx = x * 0.85f, hy = y * 0.85f + 0.04f;
    float up = bEll(hx, hy, -0.18f, -0.08f, 0.34f, 0.30f);
    up = bMin(up, bTap(hx, hy, -0.02f, -0.04f, 0.52f, 0.17f, 0.17f, 0.11f));
    up = bMin(up, bEll(hx, hy, 0.55f, 0.20f, 0.12f, 0.11f));
    up = bMin(up, bEll(hx, hy, -0.12f, 0.10f, 0.25f, 0.20f));
    float jw = bTap(hx, hy, -0.12f, 0.41f, 0.48f, 0.39f, 0.10f, 0.06f);
    float bone = bMin(up, jw);
    if (bone < 0.02f) {
        float tex = bFbm(hx * 9.0f, hy * 9.0f);
        float crack = expf(-fabsf(bFbm(hx * 5.0f + 7.0f, hy * 5.0f) - 0.5f) * 45.0f);
        float sh = 0.55f + 0.35f * tex + 0.25f * Cl(-hy * 1.2f) - 0.35f * crack;
        float cr = 0.90f * sh, cg = 0.85f * sh, cb = 0.72f * sh;
        // teeth along the front of the muzzle and the jaw
        if (hx > 0.18f && hy > 0.17f && hy < 0.30f && fabsf(Fr(hx * 22.0f) - 0.5f) > 0.43f) { cr *= 0.25f; cg *= 0.2f; cb *= 0.2f; }
        if (hx > 0.1f && hy > 0.31f && hy < 0.40f && fabsf(Fr(hx * 22.0f + 0.3f) - 0.5f) > 0.43f) { cr *= 0.25f; cg *= 0.2f; cb *= 0.2f; }
        // nostril
        float nd = bEll(hx, hy, 0.52f, 0.14f, 0.035f, 0.055f);
        bPut(cr, cg, cb, 0.02f, 0.0f, 0.0f, bEdge(nd));
        // eye socket with burning glow
        float ed = bEll(hx, hy, 0.02f, -0.06f, 0.095f, 0.12f);
        float pulse = 0.7f + 0.3f * sinf(t * 5.0f);
        bPut(cr, cg, cb, 0.05f + 0.9f * pulse * bSm(0.1f, -0.1f, ed * 8.0f), 0.02f + 0.35f * pulse * bSm(0.1f, -0.1f, ed * 8.0f), 0.0f, bEdge(ed));
        float ol = 0.35f * expf(bMin(bone, 0.0f) * 90.0f);   // dark outline
        cr *= 1.0f - ol; cg *= 1.0f - ol; cb *= 1.0f - ol;
        bPut(r, g, b, cr, cg, cb, bEdge(bone));
        // flame licking out of the eye
        float ex = hx - 0.02f, ey = hy + 0.06f;
        float fl = expf(-(ex * ex * 20.0f + ey * ey * 12.0f)) * Cl(bFbm(hx * 5.0f, hy * 5.0f + t * 3.0f) * 1.5f - 0.1f) * 0.6f;
        r += fl * bEdge(bone) * 0.0f;
    }
    // glow of the eye outside the bone is added as embers
    float em = Hh((int)((x + 1.0f) * 30), (int)((y + t * 0.8f) * 30), 3);
    if (em > 0.992f) { r += 1.0f; g += 0.6f; }
}
static void SceneOcean(float x, float y, float t, float& r, float& g, float& b) {
    float hz = -0.5f;
    if (y < hz) {
        float k = Cl((y + 1.0f) / (hz + 1.0f));
        r = bMix(0.25f, 1.0f, k * k); g = bMix(0.45f, 0.75f, k * k); b = bMix(0.85f, 0.55f, k);
        float sd = bLen(x - 0.2f, (y - hz) * 1.4f + 0.25f);
        bPut(r, g, b, 1.0f, 0.95f, 0.75f, bSm(0.2f, 0.12f, sd));
        float cl = bFbm(x * 3.0f + t * 0.1f, y * 8.0f);
        bPut(r, g, b, 1.0f, 1.0f, 1.0f, bSm(0.55f, 0.8f, cl) * 0.5f * (1.0f - k));
        return;
    }
    float z = Cl((y - hz) / (1.0f - hz));
    float xs = x / (0.25f + z);
    float depth = 1.0f / (z + 0.08f);
    float ln = sinf(depth * 3.2f - t * 2.2f + sinf(xs * 3.0f + t * 0.8f) * 0.9f);
    float ln2 = sinf(depth * 6.1f - t * 3.1f + xs * 2.0f);
    float crest = bSm(0.82f, 1.0f, ln);
    float cr = bMix(0.0f, 0.02f, z), cg = bMix(0.55f, 0.20f, z) + 0.12f * ln2, cb = bMix(0.75f, 0.42f, z);
    r = cr; g = cg; b = cb;
    float foam = crest * (0.5f + 0.5f * bFbm(xs * 7.0f, depth * 2.0f - t));
    bPut(r, g, b, 0.95f, 1.0f, 1.0f, bMin(1.0f, foam * 1.2f));
    float gl = expf(-(xs - 0.8f) * (xs - 0.8f) * 3.0f) * Cl(sinf(depth * 9.0f - t * 4.0f + xs * 6.0f)) * (1.0f - z) * 1.2f;
    r += gl; g += gl * 0.9f; b += gl * 0.6f;
    r = bMix(r, 0.7f, bSm(0.15f, 0.0f, z) * 0.5f); g = bMix(g, 0.85f, bSm(0.15f, 0.0f, z) * 0.5f); b = bMix(b, 0.9f, bSm(0.15f, 0.0f, z) * 0.5f);
}
static void SceneWaterfall(float x, float y, float t, float& r, float& g, float& b) {
    float edge = 0.50f + 0.07f * sinf(y * 7.0f + 1.0f) + 0.08f * bVn(y * 4.0f, 2.0f);
    if (y < -0.75f) {   // ledge with jungle
        float f = bFbm(x * 6.0f, y * 6.0f);
        r = 0.05f + 0.05f * f; g = 0.18f + 0.35f * f; b = 0.06f + 0.05f * f;
        if (fabsf(x) < edge) { r = bMix(r, 0.6f, 0.4f); g = bMix(g, 0.9f, 0.4f); b = bMix(b, 0.95f, 0.4f); }
        return;
    }
    if (fabsf(x) > edge) {   // rock walls
        float f = bFbm(x * 7.0f, y * 6.0f);
        float lit = 0.25f + 0.55f * f + 0.15f * (x < 0 ? 1.0f : 0.0f);
        r = lit * 0.45f; g = lit * 0.40f; b = lit * 0.38f;
        float moss = bSm(0.55f, 0.8f, bFbm(x * 4.0f + 8.0f, y * 4.0f));
        r = bMix(r, 0.05f, moss * 0.6f); g = bMix(g, 0.25f, moss * 0.6f);
        float spray = expf(-(fabsf(x) - edge) * (fabsf(x) - edge) * 60.0f) * bFbm(x * 6.0f, y * 8.0f - t * 3.0f);
        r += spray * 0.5f; g += spray * 0.5f; b += spray * 0.5f;
        return;
    }
    float s = 0.6f * bVn(x * 18.0f, y * 3.0f - t * 5.0f) + 0.4f * bVn(x * 40.0f, y * 1.2f - t * 9.0f);
    float w = Cl(s * 1.5f + 0.1f + 0.2f * sinf(x * 12.0f));
    r = bMix(0.15f, 0.95f, w * w); g = bMix(0.55f, 0.99f, w); b = bMix(0.75f, 1.0f, w);
    float poolY = 0.62f;
    if (y > poolY) {
        float rip = sinf(bLen(x * 1.5f, (y - poolY) * 4.0f) * 25.0f - t * 5.0f);
        r = bMix(0.1f, 0.4f, 0.5f + 0.5f * rip); g = bMix(0.45f, 0.85f, 0.5f + 0.5f * rip); b = bMix(0.6f, 0.95f, 0.5f + 0.5f * rip);
        float foam = bFbm(x * 9.0f, (y - t * 0.3f) * 9.0f) * bSm(poolY + 0.25f, poolY, y);
        bPut(r, g, b, 1, 1, 1, Cl(foam * 1.6f));
    }
    float mist = bFbm(x * 3.0f, y * 3.0f - t * 0.6f) * bSm(0.1f, 0.9f, y);
    bPut(r, g, b, 0.9f, 0.97f, 1.0f, mist * 0.7f);
    // rainbow in the spray
    float rd = bLen(x - 0.35f, y - 1.15f);
    float rb = expf(-(rd - 0.62f) * (rd - 0.62f) * 700.0f) * 0.45f * mist * 2.0f;
    float rr, rg, rbb; Hsv((0.62f - rd) * 6.0f, 1.0f, 1.0f, rr, rg, rbb);
    r += rr * rb; g += rg * rb; b += rbb * rb;
    float dr = Hh((int)((x + 1.0f) * 40), (int)((y - 0.5f + t * 0.5f) * 40), 8);
    if (y > 0.4f && y < 0.7f && dr > 0.985f) { r = g = b = 1.0f; }
}
static void SceneDragonEye(float x, float y, float t, float& r, float& g, float& b) {
    float k = Fr(t / 5.0f);
    float lid = k > 0.92f ? bMax(0.04f, 1.0f - sinf((k - 0.92f) / 0.08f * 3.14159f)) : 1.0f;
    float ax = fabsf(x) / 0.95f;
    float hgt = ax < 1.0f ? 0.46f * powf(1.0f - ax * ax, 0.85f) * lid : 0.0f;
    // scales around the eye
    float sx = x * 9.0f, sy = y * 9.0f;
    float row = floorf(sx); if (((int)row) & 1) sy += 0.5f;
    float fx = Fr(sx) - 0.5f, fy = Fr(sy) - 0.5f;
    float sc = 1.0f - bSm(0.25f, 0.55f, bLen(fx * 0.9f, fy));
    float shim = 0.5f + 0.5f * sinf((x + y) * 5.0f - t * 2.0f);
    float hs = Hh((int)row, (int)floorf(sy));
    r = (0.10f + 0.30f * sc) * (0.6f + 0.4f * hs) + 0.25f * sc * shim;
    g = (0.05f + 0.16f * sc) * (0.6f + 0.4f * hs);
    b = 0.03f + 0.04f * sc;
    float dl = hgt - fabsf(y);
    float edgeGlow = expf(-fabsf(dl) * 25.0f) * (ax < 1.0f ? 1.0f : 0.0f);
    r += edgeGlow * 0.9f; g += edgeGlow * 0.4f;
    if (hgt > 0.0f && fabsf(y) < hgt) {
        float rr = bLen(x, y * 0.9f), ang = atan2f(y, x);
        float fib = 0.5f + 0.5f * sinf(ang * 28.0f + bVn(rr * 10.0f, ang * 3.0f) * 5.0f);
        float ir = Cl(rr / 0.36f);
        float cr = bMix(1.0f, 0.85f, ir), cg = bMix(0.8f, 0.12f, ir), cb = bMix(0.1f, 0.0f, ir);
        float sh = 0.55f + 0.45f * fib;
        float sclera = 1.0f - bSm(0.34f, 0.38f, rr);
        float scr = 0.8f, scg = 0.55f, scb = 0.15f;
        float shade = 0.5f + 0.5f * Cl(dl * 6.0f);
        float er = bMix(scr, cr * sh, sclera) * shade, eg = bMix(scg, cg * sh, sclera) * shade, eb = bMix(scb, cb * sh, sclera) * shade;
        float prx = 0.045f + 0.035f * sinf(t * 1.5f);
        float pu = x / prx, pv = y / 0.30f;
        float pup = bSm(1.0f, 0.82f, pu * pu + pv * pv);
        er *= 1.0f - pup; eg *= 1.0f - pup; eb *= 1.0f - pup;
        float hl = bSm(0.06f, 0.02f, bLen(x + 0.11f, (y + 0.12f) * 1.3f));
        er += hl; eg += hl; eb += hl;
        float inl = bSm(0.0f, 0.02f, dl);
        r = bMix(r, er, inl); g = bMix(g, eg, inl); b = bMix(b, eb, inl);
    }
}
static void SceneGalaxy(float x, float y, float t, float& r, float& g, float& b) {
    float yy = y * 1.35f;
    float rr = bLen(x, yy), ang = atan2f(yy, x) + t * 0.22f;
    float arm = 0.5f + 0.5f * cosf(2.0f * ang - 5.2f * logf(rr + 0.03f));
    arm = arm * arm * arm;
    float dust = bFbm(x * 6.0f + t * 0.05f, y * 6.0f);
    float core = expf(-rr * 7.0f);
    float disc = expf(-rr * 2.3f);
    float a = arm * disc * (0.5f + 0.9f * dust);
    r = 1.0f * core * 1.6f + 0.35f * a * 1.4f + 0.18f * disc * 0.3f;
    g = 0.8f * core * 1.6f + 0.45f * a * 1.4f + 0.12f * disc * 0.3f;
    b = 0.5f * core * 1.6f + 1.00f * a * 1.4f + 0.30f * disc * 0.3f;
    r += 0.9f * a * bSm(0.55f, 0.75f, bFbm(x * 3.0f + 4.0f, y * 3.0f - t * 0.1f)) * 0.5f;   // pink nebulae
    b += 0.5f * a * bSm(0.55f, 0.75f, bFbm(x * 3.0f + 4.0f, y * 3.0f - t * 0.1f)) * 0.5f;
    int cx = (int)floorf((x + 1.0f) * 36.0f), cy = (int)floorf((y + 1.0f) * 36.0f);
    float hh = Hh(cx, cy, 6);
    if (hh > 0.9f) {
        float fx = (x + 1.0f) * 36.0f - cx - 0.5f, fy = (y + 1.0f) * 36.0f - cy - 0.5f;
        float tw = 0.5f + 0.5f * sinf(t * 3.0f + hh * 60.0f);
        float s = expf(-(fx * fx + fy * fy) * 22.0f) * tw;
        r += s; g += s; b += s * 0.9f;
    }
}
static void SceneLavaCracks(float x, float y, float t, float& r, float& g, float& b) {
    float px = x * 3.2f, py = y * 3.2f;
    int ci = (int)floorf(px), cj = (int)floorf(py);
    float d1 = 9.0f, d2 = 9.0f, hid = 0;
    for (int j = -1; j <= 1; j++)
        for (int i = -1; i <= 1; i++) {
            float h1 = Hh(ci + i, cj + j, 21), h2 = Hh(ci + i, cj + j, 22);
            float qx = ci + i + 0.5f + 0.38f * sinf(t * 0.35f + h1 * 6.28f);
            float qy = cj + j + 0.5f + 0.38f * cosf(t * 0.30f + h2 * 6.28f);
            float d = bLen(px - qx, py - qy);
            if (d < d1) { d2 = d1; d1 = d; hid = h1; } else if (d < d2) d2 = d;
        }
    float edge = d2 - d1;
    float glow = expf(-edge * 11.0f);
    float heat = glow * (0.65f + 0.35f * sinf(t * 2.2f + hid * 8.0f + edge * 6.0f));
    float rock = 0.05f + 0.10f * bFbm(x * 9.0f, y * 9.0f) + 0.06f * hid;
    r = rock + heat * 1.6f; g = rock * 0.7f + heat * heat * 0.9f + heat * 0.15f; b = rock * 0.6f + heat * heat * heat * 0.4f;
    float em = Hh((int)((x + 1.0f) * 28), (int)((y + t * 0.6f) * 28), 5);
    if (em > 0.99f) { r += 1.0f; g += 0.5f; }
}
static void SceneKoi(float x, float y, float t, float& r, float& g, float& b) {
    float rip = sinf(bLen(x - 0.5f, y + 0.3f) * 30.0f - t * 3.0f) + sinf(bLen(x + 0.6f, y - 0.5f) * 26.0f - t * 2.4f);
    float wv = bFbm(x * 4.0f + t * 0.1f, y * 4.0f - t * 0.1f);
    r = 0.02f + 0.03f * wv; g = 0.18f + 0.18f * wv + 0.05f * rip; b = 0.25f + 0.2f * wv + 0.05f * rip;
    // lily pads
    static const float LP[3][3] = {{-0.55f, -0.45f, 0.22f}, {0.6f, 0.5f, 0.26f}, {0.55f, -0.6f, 0.17f}};
    for (int i = 0; i < 3; i++) {
        float lx = LP[i][0] + 0.02f * sinf(t * 0.7f + i), ly = LP[i][1] + 0.02f * cosf(t * 0.6f + i);
        float dd = bLen(x - lx, y - ly) - LP[i][2];
        float ang = atan2f(y - ly, x - lx);
        bool notch = fabsf(ang - 0.6f * i) < 0.18f;
        if (dd < 0 && !notch) { float v = 0.5f + 0.5f * bVn(x * 20, y * 20); bPut(r, g, b, 0.06f + 0.05f * v, 0.35f + 0.15f * v, 0.10f, 1.0f); }
        float fl = bLen(x - lx - 0.05f, y - ly + 0.03f);
        if (i == 0 && fl < 0.06f) bPut(r, g, b, 1.0f, 0.6f + 0.4f * bSm(0.0f, 0.06f, fl), 0.85f, 1.0f);
    }
    // three koi swimming in circles
    static const float KC[3][5] = {{0.0f, 0.0f, 0.55f, 0.7f, 0.0f}, {0.1f, -0.1f, 0.4f, -0.9f, 2.0f}, {-0.1f, 0.15f, 0.7f, 0.55f, 4.0f}};
    for (int k = 0; k < 3; k++) {
        float w = KC[k][3], ph = KC[k][4];
        float a0 = t * w + ph;
        float dir = w > 0 ? 1.0f : -1.0f;
        float ringD = fabsf(bLen(x - KC[k][0], y - KC[k][1]) - KC[k][2]);
        if (ringD > 0.22f) continue;
        float best = 9.0f; int seg = 0;
        for (int i = 0; i < 6; i++) {
            float a = a0 - dir * i * 0.075f / KC[k][2] * 1.0f;
            float side = 0.035f * sinf(t * 6.0f - i * 0.9f + k) * (0.3f + i * 0.2f);
            float rad = KC[k][2] + side;
            float cx = KC[k][0] + rad * cosf(a), cy = KC[k][1] + rad * sinf(a);
            float R = (i == 0 ? 0.055f : (i < 4 ? 0.07f - i * 0.006f : 0.05f - (i - 4) * 0.02f));
            float d = bLen(x - cx, y - cy) - R;
            if (d < best) { best = d; seg = i; }
        }
        if (best < 0.02f) {
            float cr, cg, cb;
            if (k == 0) { cr = 1.0f; cg = 0.45f; cb = 0.1f; if (seg == 2 || seg == 4) { cr = 1.0f; cg = 0.95f; cb = 0.9f; } }
            else if (k == 1) { cr = 1.0f; cg = 0.97f; cb = 0.92f; if (seg == 1 || seg == 3) { cr = 0.9f; cg = 0.15f; cb = 0.1f; } }
            else { cr = 0.12f; cg = 0.12f; cb = 0.14f; if (seg == 2) { cr = 1.0f; cg = 0.6f; cb = 0.1f; } }
            float sh = 0.8f + 0.2f * bSm(0.0f, -0.05f, best);
            bPut(r, g, b, cr * sh, cg * sh, cb * sh, bEdge(best));
        }
        // tail fin trailing behind the last segment
        float a = a0 - dir * 6.0f * 0.075f / KC[k][2] - dir * 0.08f;
        float rad = KC[k][2] + 0.04f * sinf(t * 6.0f - 5.4f + k);
        float tx = KC[k][0] + rad * cosf(a), ty = KC[k][1] + rad * sinf(a);
        float fd = bLen(x - tx, (y - ty) * 1.4f) - 0.06f;
        if (fd < 0 && bLen(x - KC[k][0], y - KC[k][1]) > 0.0f) bPut(r, g, b, k == 2 ? 0.2f : 1.0f, k == 2 ? 0.2f : 0.7f, k == 2 ? 0.25f : 0.5f, 0.45f * bSm(0.0f, -0.05f, fd));
    }
    float sp = bMax(0.0f, rip - 1.5f) * 0.25f;
    r += sp; g += sp; b += sp;
}
static void SceneStorm(float x, float y, float t, float& r, float& g, float& b) {
    float k = t * 1.1f;
    int ki = (int)floorf(k);
    float kf = k - ki;
    float flash = (kf < 0.18f ? 1.0f - kf / 0.18f : 0.0f) * (Hh(ki, 3) > 0.35f ? 1.0f : 0.0f);
    flash *= 0.7f + 0.3f * sinf(t * 90.0f);
    float cl = bFbm(x * 2.2f + t * 0.25f, y * 2.5f - t * 0.05f);
    float dark = bMix(0.05f, 0.35f, cl) * (1.0f - 0.4f * bSm(0.0f, 1.0f, y));
    r = dark * 0.8f + flash * 0.5f * cl; g = dark * 0.85f + flash * 0.5f * cl; b = dark + 0.15f + flash * 0.7f * cl;
    // lightning bolt with branches
    float bx0 = (Hh(ki, 1) - 0.5f) * 1.2f;
    if (Hh(ki, 3) > 0.35f && kf < 0.35f) {
        float yy = (y + 1.0f) * 9.0f;
        int row = (int)floorf(yy);
        float fy = yy - row;
        float xa = bx0 + (Hh(row, ki, 2) - 0.5f) * 0.25f, xb = bx0 + (Hh(row + 1, ki, 2) - 0.5f) * 0.25f;
        float acc = 0.0f;
        // accumulate offsets to make a connected jagged path
        float off = 0.0f;
        for (int i = 0; i < row && i < 18; i++) off += (Hh(i, ki, 2) - 0.5f) * 0.22f;
        float xs = bx0 + off + (Hh(row, ki, 2) - 0.5f) * 0.22f * fy;
        (void)xa; (void)xb; (void)acc;
        float d = fabsf(x - xs);
        float vis = (kf < 0.18f ? 1.0f : 1.0f - (kf - 0.18f) / 0.17f);
        float bolt = (expf(-d * d * 4000.0f) + 0.35f * expf(-d * d * 200.0f)) * vis;
        r += bolt * 0.9f; g += bolt * 0.9f; b += bolt * 1.0f;
        // a side branch
        float bd = fabsf((x - xs) - (y - (row / 9.0f - 1.0f)) * 0.9f * ((Hh(row, ki, 5) > 0.5f) ? 1.0f : -1.0f));
        if (Hh(row, ki, 4) > 0.6f && y > row / 9.0f - 1.0f && y < row / 9.0f - 1.0f + 0.25f)
            { float bb = expf(-bd * bd * 3000.0f) * vis * 0.7f; r += bb * 0.8f; g += bb * 0.8f; b += bb; }
    }
    // rain
    float rx = x * 40.0f + y * 8.0f;
    int rc = (int)floorf(rx);
    float rh = Hh(rc, 9);
    float ry = Fr(y * 1.2f - t * (2.5f + rh * 1.5f) + rh * 5.0f);
    float rain = (Fr(rx) > 0.4f && Fr(rx) < 0.55f && ry < 0.12f) ? (1.0f - ry / 0.12f) : 0.0f;
    float rh2 = rh > 0.5f ? 1.0f : 0.0f;
    r += rain * 0.35f * rh2; g += rain * 0.4f * rh2; b += rain * 0.55f * rh2;
}
static void SceneBlackHole(float x, float y, float t, float& r, float& g, float& b) {
    float rr = bLen(x, y);
    float lens = 1.0f + 0.045f / (rr * rr + 0.01f);
    float wx = x * lens, wy = y * lens;
    r = g = b = 0.0f;
    int cx = (int)floorf((wx + 2.0f) * 30.0f), cy = (int)floorf((wy + 2.0f) * 30.0f);
    float hh = Hh(cx, cy, 6);
    if (hh > 0.93f) {
        float fx = (wx + 2.0f) * 30.0f - cx - 0.5f, fy = (wy + 2.0f) * 30.0f - cy - 0.5f;
        float s = expf(-(fx * fx + fy * fy) * 20.0f) * (0.6f + 0.4f * sinf(t * 3.0f + hh * 50.0f));
        r = s * 0.8f; g = s * 0.85f; b = s;
    }
    float ang = atan2f(y, x);
    // accretion disc seen almost edge-on + the lensed upper/lower arcs
    float dy = y * 4.5f;
    float dd = bLen(x, dy);
    float swirl = 0.5f + 0.5f * sinf(atan2f(dy, x) * 3.0f - t * 3.0f + dd * 14.0f);
    float disc = bSm(0.18f, 0.28f, dd) * bSm(0.85f, 0.45f, dd);
    float band = disc * (0.6f + 0.6f * swirl) * (y * y < 0.012f ? 1.0f : expf(-(fabsf(y) - 0.1f) * 12.0f));
    float dop = 0.5f + 0.5f * (x > 0 ? 1.0f : 0.0f) * 0.6f;
    r += band * 1.7f * dop; g += band * 0.75f * dop; b += band * 0.25f;
    float ring = expf(-(rr - 0.2f) * (rr - 0.2f) * 900.0f);
    float arcs = expf(-(rr - 0.24f) * (rr - 0.24f) * 250.0f) * (0.5f + 0.5f * sinf(ang * 2.0f + t * 2.0f)) * 0.35f;
    r += ring * 1.4f + arcs; g += ring * 0.9f + arcs * 0.6f; b += ring * 0.6f + arcs * 0.2f;
    float body = bSm(0.2f, 0.17f, rr);
    r *= 1.0f - body; g *= 1.0f - body; b *= 1.0f - body;
}
static void SceneJelly(float x, float y, float t, float& r, float& g, float& b) {
    r = 0.0f; g = 0.03f + 0.06f * (y + 1.0f) * 0.5f; b = 0.12f + 0.14f * (1.0f - (y + 1.0f) * 0.5f);
    float sn = Hh((int)((x + 1.0f) * 24), (int)((y + t * 0.15f) * 24), 7);
    if (sn > 0.985f) { r += 0.4f; g += 0.6f; b += 0.7f; }
    static const float J[3][4] = {{-0.5f, -0.1f, 0.34f, 0.0f}, {0.45f, 0.25f, 0.28f, 2.1f}, {0.0f, -0.65f, 0.2f, 4.2f}};
    for (int j = 0; j < 3; j++) {
        float ph = t * 1.6f + J[j][3];
        float pulse = 0.5f + 0.5f * sinf(ph);
        float cx = J[j][0] + 0.04f * sinf(t * 0.5f + J[j][3]), cy = J[j][1] - 0.10f * pulse + 0.03f * sinf(t * 0.7f);
        float R = J[j][2] * (1.0f - 0.18f * pulse);
        float H = J[j][2] * (0.8f + 0.22f * pulse);
        if (fabsf(x - cx) > R + 0.3f || y < cy - H - 0.15f || y > cy + 0.95f) continue;
        float dx = (x - cx) / R, dy = (y - cy) / H;
        float hue = 0.82f + 0.12f * j;
        float cr, cg, cb; Hsv(hue + 0.05f * sinf(t + j), 0.6f, 1.0f, cr, cg, cb);
        if (dy < 0.08f) {
            float q = dx * dx + dy * dy;
            if (q < 1.0f) {
                float rib = 0.5f + 0.5f * sinf(atan2f(dy, dx) * 14.0f);
                float inner = 0.25f + 0.35f * rib * (1.0f - q) + 0.5f * bSm(0.55f, 1.0f, q);
                float a = bSm(1.0f, 0.93f, q);
                bPut(r, g, b, cr * inner + 0.1f, cg * inner + 0.1f, cb * inner + 0.2f, a * 0.85f);
                float gl2 = expf(-(dx * dx + (dy + 0.3f) * (dy + 0.3f)) * 6.0f) * 0.35f;
                r += cr * gl2; g += cg * gl2; b += cb * gl2;
            }
            float halo = expf(-(q - 1.0f) * (q - 1.0f) * 12.0f) * 0.25f;
            r += cr * halo; g += cg * halo; b += cb * halo;
        }
        // tentacles
        float ty = (y - (cy + 0.02f * H));
        if (ty > 0.0f && ty < 0.75f) {
            for (int k = 0; k < 6; k++) {
                float off = (k - 2.5f) * R * 0.34f;
                float tx = cx + off + 0.05f * sinf(ty * 9.0f - t * 3.0f + k * 1.3f + J[j][3]) * (0.4f + ty);
                float d = fabsf(x - tx);
                float strand = expf(-d * d * 6000.0f) * (1.0f - ty / 0.75f);
                float bead = bSm(0.7f, 1.0f, sinf(ty * 40.0f - t * 6.0f + k)) * 0.5f;
                r += cr * strand * (0.5f + bead); g += cg * strand * (0.5f + bead); b += cb * strand * (0.5f + bead);
            }
        }
    }
}
static void ScenePeacock(float x, float y, float t, float& r, float& g, float& b) {
    float sx = (x + 1.0f) * 1.5f, sy = (y + 1.0f) * 1.5f;
    float row = floorf(sy);
    float fx = sx + (((int)row) & 1 ? 0.5f : 0.0f);
    float ci = floorf(fx), cxl = Fr(fx) - 0.5f, cyl = Fr(sy) - 0.5f;
    float ex = cxl, ey = cyl * 1.15f;
    float e = bLen(ex, ey * 0.85f);
    float shim = 0.5f + 0.5f * sinf(t * 1.6f + ci * 1.7f + row * 2.3f);
    float ang = atan2f(cyl, cxl);
    // barbs: fine radiating lines around the eye
    float barb = 0.5f + 0.5f * sinf(ang * 40.0f + bVn(e * 8.0f, ang * 2.0f + t * 0.3f) * 3.0f);
    float hueS = 0.38f + 0.12f * sinf(t * 0.6f + (x + y) * 2.5f);
    float cr, cg, cb; Hsv(hueS, 0.9f, 0.35f + 0.45f * barb, cr, cg, cb);
    // golden fringe
    float fr = bSm(0.30f, 0.42f, e);
    cr = bMix(cr, 0.75f * barb + 0.15f, fr * 0.7f); cg = bMix(cg, 0.55f * barb + 0.1f, fr * 0.7f); cb = bMix(cb, 0.1f, fr * 0.7f);
    // the eye: bronze ring, green ring, teal ring, deep blue core
    if (e < 0.30f) {
        float ec = 0.55f + 0.2f * shim;
        if (e < 0.06f) { cr = 0.03f; cg = 0.03f; cb = 0.35f + 0.3f * shim; }
        else if (e < 0.12f) { cr = 0.05f; cg = 0.45f * ec; cb = 0.8f * ec; }
        else if (e < 0.19f) { cr = 0.05f; cg = 0.6f * ec; cb = 0.25f; }
        else if (e < 0.25f) { cr = 0.75f * ec; cg = 0.55f * ec; cb = 0.1f; }
        else { cr = 0.25f; cg = 0.4f; cb = 0.15f; }
    }
    float swp = expf(-powf(Fr(x * 0.3f - y * 0.3f - t * 0.2f) - 0.5f, 2.0f) * 60.0f) * 0.35f;
    r = cr + swp * 0.6f; g = cg + swp; b = cb + swp * 0.6f;
}
static void SceneDragonScales(float x, float y, float t, float& r, float& g, float& b) {
    float N = 9.0f;
    float sy = (y + 1.0f) * 0.5f * N;
    float row = floorf(sy);
    float sx = (x + 1.0f) * 0.5f * N * 0.9f + (((int)row) & 1 ? 0.5f : 0.0f);
    float fx = Fr(sx) - 0.5f, fy = Fr(sy);
    float cxi = floorf(sx);
    float d = bLen(fx, fy - 0.12f);          // scale = round bottom, overlapping rows
    float inScale = bSm(0.62f, 0.5f, d);
    float rim = bSm(0.46f, 0.58f, d) * inScale;
    float hs = Hh((int)cxi, (int)row, 3);
    float wave = Fr(((x + y) * 0.5f) * 0.9f - t * 0.35f);
    float fire = expf(-powf(wave - 0.5f, 2.0f) * 40.0f);
    float shade = 0.25f + 0.5f * (1.0f - d * 1.2f) + 0.2f * hs;
    r = 0.30f * shade + 0.1f; g = 0.03f * shade; b = 0.02f * shade;
    r += fire * (0.4f + 0.9f * rim); g += fire * (0.12f + 0.5f * rim); b += fire * 0.05f;
    r += rim * 0.35f; g += rim * 0.10f;
    float spec = bSm(0.35f, 0.15f, bLen(fx + 0.1f, fy - 0.0f)) * 0.25f * (0.5f + 0.5f * sinf(t * 2.0f + hs * 20.0f));
    r += spec; g += spec * 0.5f; b += spec * 0.3f;
    float em = Hh((int)((x + 1.0f) * 30), (int)((y + t * 0.7f) * 30), 9);
    if (em > 0.992f) { r += 1.0f; g += 0.55f; }
    r *= 0.25f + 0.75f * inScale; g *= 0.25f + 0.75f * inScale; b *= 0.25f + 0.75f * inScale;
}
// u,v in [0,1]; the scene works in x,y in [-1,1] (y down)
static void ScenePixel(int id, float u, float v, float t, float& r, float& g, float& b) {
    float x = u * 2.0f - 1.0f, y = v * 2.0f - 1.0f;
    r = g = b = 0.0f;
    switch (id) {
        case 45: SceneHorse(x, y, t, r, g, b); break;
        case 46: SceneHorseSkull(x, y, t, r, g, b); break;
        case 47: SceneUnicorn(x, y, t, r, g, b); break;
        case 48: SceneOcean(x, y, t, r, g, b); break;
        case 49: SceneWaterfall(x, y, t, r, g, b); break;
        case 50: SceneDragonEye(x, y, t, r, g, b); break;
        case 51: SceneGalaxy(x, y, t, r, g, b); break;
        case 52: SceneLavaCracks(x, y, t, r, g, b); break;
        case 53: SceneKoi(x, y, t, r, g, b); break;
        case 54: SceneStorm(x, y, t, r, g, b); break;
        case 55: SceneBlackHole(x, y, t, r, g, b); break;
        case 56: SceneJelly(x, y, t, r, g, b); break;
        case 57: ScenePeacock(x, y, t, r, g, b); break;
        default: SceneDragonScales(x, y, t, r, g, b); break;
    }
}

static uint32_t Pixel(int design, float u, float v, float t) {
    float r = 0, g = 0, b = 0;
    const float kPi = 3.14159265f;
    int mv = MatVariant(design);
    if (mv >= 0) { MatrixPixel(mv, u, v, t, r, g, b); return Pack(r, g, b); }
    if (design >= 45) { ScenePixel(design, u, v, t, r, g, b); return Pack(r, g, b); }
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
        case 4: {
            float su = u * 4 + t * 0.25f, sv = v * 4;
            int id = (int)(Hh((int)floorf(su), (int)floorf(sv)) * 5) % 5;
            float x = (su - floorf(su)) * 2 - 1, y = (sv - floorf(sv)) * 2 - 1;
            if (Shape(id, x, y)) Hsv(t * 0.2f + id * 0.2f, 0.9f, 1, r, g, b);
            else { Hsv(t * 0.1f + v * 0.3f, 0.8f, 0.25f, r, g, b); }
            break;
        }
        case 5: {
            float d1 = fabsf(Fr(u * 3 + v * 3 + t * 0.5f) - 0.5f);
            float d2 = fabsf(Fr(u * 2 - v * 2 - t * 0.4f) - 0.5f);
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
            // Fr() keeps the ring phase positive for any t (fmodf went negative after a few seconds => black car)
            float q = Fr(rr * 4 - t * 1.2f) - 0.5f;
            float in = expf(-q * q * 90) + 0.05f;
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

// ---------------- animated paint slots ----------------
// every animated design that is used on the car owns one small dynamic texture; several can run at once
static const int MAX_DYN = 8;
struct DynSlot { int design; RwRaster* raster; RwTexture* tex; };
static std::vector<DynSlot> g_dyns;

static void DynFill(DynSlot& d) {
    if (!d.raster) return;
    float t = CTimer::m_snTimeInMilliseconds / 1000.0f;
    RwUInt8* px = RwRasterLock(d.raster, 0, rwRASTERLOCKWRITE);
    if (!px) return;
    int stride = RwRasterGetStride(d.raster);
    int st = DesignIsScene(d.design) ? 2 : 1;      // the big scenes are drawn at 128x128 and doubled (much cheaper)
    for (int y = 0; y < DYN_SIZE; y += st) {
        uint32_t* row = (uint32_t*)(px + y * stride);
        for (int x = 0; x < DYN_SIZE; x += st) {
            uint32_t c = Pixel(d.design, (x + st * 0.5f) / DYN_SIZE, (y + st * 0.5f) / DYN_SIZE, t);
            row[x] = c;
            if (st == 2) row[x + 1] = c;
        }
        if (st == 2) memcpy(px + (y + 1) * stride, row, DYN_SIZE * 4);
    }
    RwRasterUnlock(d.raster);
}
// live preview in the menu: one extra texture that is not counted in MAX_DYN
static DynSlot g_prevSlot = {-1, nullptr, nullptr};
static RwTexture* PreviewTex(int design) {
    if (!g_prevSlot.raster) {
        g_prevSlot.raster = RwRasterCreate(DYN_SIZE, DYN_SIZE, 32, rwRASTERTYPETEXTURE | rwRASTERFORMAT8888);
        if (!g_prevSlot.raster) return nullptr;
        g_prevSlot.tex = RwTextureCreate(g_prevSlot.raster);
        if (!g_prevSlot.tex) return nullptr;
        strncpy(g_prevSlot.tex->name, "bt_prev", 31);
        RwTextureSetFilterMode(g_prevSlot.tex, rwFILTERLINEAR);
        RwTextureSetAddressing(g_prevSlot.tex, rwTEXTUREADDRESSWRAP);
        g_prevSlot.design = -1;
    }
    static unsigned lastMs = 0;
    unsigned now = CTimer::m_snTimeInMilliseconds;
    if (g_prevSlot.design != design || now - lastMs >= 50 || now < lastMs) {
        g_prevSlot.design = design;
        lastMs = now;
        DynFill(g_prevSlot);
    }
    return g_prevSlot.tex;
}
static bool DesignInUse(int design) {
    for (auto& r : g_recs) if (r.on && r.asgKind == 2 && r.asgDesign == design) return true;
    return false;
}
static DynSlot* DynGet(int design) {
    if (g_dyns.capacity() < (size_t)MAX_DYN) g_dyns.reserve(MAX_DYN);
    for (auto& d : g_dyns) if (d.design == design) return &d;
    if ((int)g_dyns.size() >= MAX_DYN) {
        for (auto& d : g_dyns)
            if (!DesignInUse(d.design)) { d.design = design; DynFill(d); return &d; }   // recycle an unused one
        return nullptr;
    }
    DynSlot d = {};
    d.design = design;
    d.raster = RwRasterCreate(DYN_SIZE, DYN_SIZE, 32, rwRASTERTYPETEXTURE | rwRASTERFORMAT8888);
    if (!d.raster) return nullptr;
    d.tex = RwTextureCreate(d.raster);
    if (!d.tex) return nullptr;
    strncpy(d.tex->name, "bt_dyn", 31);
    RwTextureSetFilterMode(d.tex, rwFILTERLINEAR);
    RwTextureSetAddressing(d.tex, rwTEXTUREADDRESSWRAP);
    DynFill(d);
    g_dyns.push_back(d);
    return &g_dyns.back();
}
// called every frame: each used design is redrawn every DYN_EVERY frames, staggered so the cost is spread out
static void UpdateDyns() {
    ++g_frame;
    int i = 0;
    for (auto& d : g_dyns) {
        if (!DesignInUse(d.design)) continue;
        if (g_frame % DYN_EVERY == i % DYN_EVERY) DynFill(d);
        i++;
    }
}

// ---------------- per-part texture assignment ----------------
static void ReleaseAsg(MatRec& r) {
    if (r.asgKind == 1 && r.asgTex) {
        RwTextureDestroy(r.asgTex);
        if (r.asgSlot >= 0) {
            CTxdStore::RemoveRef(r.asgSlot);
            if (r.asgOwn) CStreaming::SetModelIsDeletable(20000 + r.asgSlot);
        }
    }
    r.asgKind = 0; r.asgTex = nullptr; r.asgSlot = -1; r.asgOwn = false; r.asgDesign = 0; r.asgTxd[0] = 0;
}
// the TXD stays referenced while any part uses one of its textures, so the streamer cannot unload it
static void AssignTexSlot(MatRec& r, RwTexture* t, int slot, bool own, const char* txdName) {
    if (!t) return;
    if (r.asgKind == 1 && r.asgTex == t) return;
    ReleaseAsg(r);
    r.asgKind = 1; r.asgTex = t;
    t->refCount++;
    r.asgSlot = slot; r.asgOwn = own;
    if (slot >= 0) CTxdStore::AddRef(slot);
    strncpy(r.asgTxd, txdName ? txdName : "", sizeof(r.asgTxd) - 1);
    r.asgTxd[sizeof(r.asgTxd) - 1] = 0;
}
static void AssignTex(MatRec& r, RwTexture* t) {
    AssignTexSlot(r, t, g_slot, g_weLoaded, g_openName);
}
static bool AssignDesign(MatRec& r, int d) {
    if (r.asgKind == 2 && r.asgDesign == d) return true;
    if (!DynGet(d)) { Status("max %d different animated designs at once", MAX_DYN); return false; }
    ReleaseAsg(r);
    r.asgKind = 2; r.asgDesign = d;
    return true;
}
// the current selection: category 1 = highlighted game texture, category 2 = chosen design
static bool SelValid() { return g_mode == 1 ? CurTex() != nullptr : g_mode == 2; }
static bool AssignSel(MatRec& r) {
    if (g_mode == 1) { RwTexture* t = CurTex(); if (!t) return false; AssignTex(r, t); return true; }
    if (g_mode == 2) return AssignDesign(r, g_design);
    return false;
}

// ---------------- apply / restore ----------------
static void ApplyPart(MatRec& r) {
    RwTexture* tex = nullptr;
    bool glow = false;
    if (r.on && r.asgKind == 1) tex = r.asgTex;
    else if (r.on && r.asgKind == 2) {
        DynSlot* d = DynGet(r.asgDesign);
        if (d) tex = d->tex;
        glow = DesignIsGlow(r.asgDesign);
    }
    if (tex) {
        if (RpMaterialGetTexture(r.mat) != tex) RpMaterialSetTexture(r.mat, tex);
        if (glow) {
            RwSurfaceProperties gp;
            gp.ambient = 2.5f; gp.specular = 0.0f; gp.diffuse = 0.0f;
            RpMaterialSetSurfaceProperties(r.mat, &gp);
        } else RpMaterialSetSurfaceProperties(r.mat, &r.origProps);
    } else {
        if (RpMaterialGetTexture(r.mat) != r.origTex) RpMaterialSetTexture(r.mat, r.origTex);
        RpMaterialSetSurfaceProperties(r.mat, &r.origProps);
    }
}
static void ApplyAll() {
    if (!g_veh) return;
    for (auto& r : g_recs) ApplyPart(r);
}
// "Apply to all parts": the selection goes onto every active part; parts are changed one by one afterwards
static void ApplySelToAll() {
    if (!g_veh) { Status("get into a car first"); return; }
    if (!SelValid()) { Status("select a texture first"); return; }
    int n = 0;
    for (auto& r : g_recs) if (r.on && r.canUse && AssignSel(r)) n++;
    ApplyAll();
    Status("applied to %d parts", n);
}
static void Release() {
    g_loadedName[0] = 0;
    bool ok = g_veh && VehicleAlive(g_veh) && g_veh->m_nModelIndex == g_vehModel;
    for (auto& r : g_recs) {
        if (ok) {
            RpMaterialSetTexture(r.mat, r.origTex);
            RpMaterialSetSurfaceProperties(r.mat, &r.origProps);
            if (r.origTex) RwTextureDestroy(r.origTex);
        }
        ReleaseAsg(r);
    }
    if (ok) {
        g_veh->m_nPrimaryColor = g_origCols[0];
        g_veh->m_nSecondaryColor = g_origCols[1];
        g_veh->m_nTertiaryColor = g_origCols[2];
        g_veh->m_nQuaternaryColor = g_origCols[3];
    } else if (g_veh) {
        Log("vehicle gone, dropping %d records without restore", (int)g_recs.size());
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
    // a new car gets the current selection on all its active parts (same as before); change parts one by one afterwards
    if (g_mode == 2 || (g_mode == 1 && CurTex()))
        for (auto& r : g_recs) if (r.on && r.canUse) AssignSel(r);
    ApplyAll();
}

// ---------------- saves: car id + the texture of every part (game texture or animated design) ----------------
static const char* SAVE_FILE = "BodyTex_saves.txt";
struct SavePart {
    char frame[40];
    int occ;        // which material of that frame (0 = first one)
    int on;
    int kind;       // 0 original, 1 game texture, 2 animated design
    int design;
    char txd[24];
    char tex[32];
};
struct SaveEnt {
    char name[32] = {0};
    int model = -1;
    std::vector<SavePart> parts;
};
static std::vector<SaveEnt> g_saves;
static bool g_savesLoaded = false;

static int SplitBar(char* str, char** out, int maxn) {
    int n = 0;
    out[n++] = str;
    for (char* q = str; *q && n < maxn; q++)
        if (*q == '|') { *q = 0; out[n++] = q + 1; }
    return n;
}
static void LoadSaves() {
    g_savesLoaded = true;
    g_saves.clear();
    FILE* f = fopen(SAVE_FILE, "r");
    if (!f) return;
    char line[512];
    int cur = -1;
    while (fgets(line, sizeof(line), f)) {
        TrimInPlace(line);
        if (!line[0]) continue;
        if (!strcmp(line, "[save]")) { g_saves.emplace_back(); cur = (int)g_saves.size() - 1; continue; }
        if (cur < 0) continue;
        SaveEnt& e = g_saves[cur];
        if (!strncmp(line, "name=", 5)) { strncpy(e.name, line + 5, sizeof(e.name) - 1); e.name[sizeof(e.name) - 1] = 0; }
        else if (!strncmp(line, "model=", 6)) e.model = atoi(line + 6);
        else if (!strncmp(line, "part=", 5)) {
            char buf[400];
            strncpy(buf, line + 5, sizeof(buf) - 1); buf[sizeof(buf) - 1] = 0;
            char* fl[8];
            int nf = SplitBar(buf, fl, 8);
            if (nf >= 7) {
                SavePart sp; memset(&sp, 0, sizeof(sp));
                strncpy(sp.frame, fl[0], sizeof(sp.frame) - 1);
                sp.occ = atoi(fl[1]); sp.on = atoi(fl[2]); sp.kind = atoi(fl[3]); sp.design = atoi(fl[4]);
                strncpy(sp.txd, fl[5], sizeof(sp.txd) - 1);
                strncpy(sp.tex, fl[6], sizeof(sp.tex) - 1);
                e.parts.push_back(sp);
            }
        }
    }
    fclose(f);
    for (int i = (int)g_saves.size() - 1; i >= 0; i--)
        if (!g_saves[i].name[0] || g_saves[i].model < 0) g_saves.erase(g_saves.begin() + i);
    Log("saves loaded: %d", (int)g_saves.size());
}
static bool WriteSaves() {
    FILE* f = fopen(SAVE_FILE, "w");
    if (!f) return false;
    for (auto& e : g_saves) {
        fprintf(f, "[save]\nname=%s\nmodel=%d\n", e.name, e.model);
        for (auto& p : e.parts)
            fprintf(f, "part=%s|%d|%d|%d|%d|%s|%s\n", p.frame, p.occ, p.on, p.kind, p.design, p.txd, p.tex);
        fprintf(f, "\n");
    }
    fclose(f);
    return true;
}
// stores the car id and every part that differs from the default (on/off, game texture, animated design)
static bool SaveCurrent(const char* nameIn) {
    if (!g_veh || g_recs.empty() || g_mode == 0) { ShowError("Get into a car and paint it first"); return false; }
    char nm[32];
    strncpy(nm, nameIn, sizeof(nm) - 1); nm[sizeof(nm) - 1] = 0;
    TrimInPlace(nm);
    if (!nm[0]) { ShowError("Type a name for the save"); return false; }
    SaveEnt e;
    strncpy(e.name, nm, sizeof(e.name) - 1);
    e.model = g_vehModel;
    int texCnt = 0;
    for (size_t i = 0; i < g_recs.size(); i++) {
        const MatRec& r = g_recs[i];
        if (r.on == r.autoOn && r.asgKind == 0) continue;
        SavePart sp; memset(&sp, 0, sizeof(sp));
        strncpy(sp.frame, r.frame, sizeof(sp.frame) - 1);
        int occ = 0;
        for (size_t j = 0; j < i; j++) if (!strcmp(g_recs[j].frame, r.frame)) occ++;
        sp.occ = occ;
        sp.on = r.on ? 1 : 0;
        if (r.asgKind == 1 && r.asgTex && r.asgTxd[0]) {
            sp.kind = 1;
            strncpy(sp.txd, r.asgTxd, sizeof(sp.txd) - 1);
            strncpy(sp.tex, r.asgTex->name, sizeof(sp.tex) - 1);
            texCnt++;
        } else if (r.asgKind == 2) {
            sp.kind = 2; sp.design = r.asgDesign;
            texCnt++;
        }
        e.parts.push_back(sp);
    }
    if (!texCnt) { ShowError("Nothing is textured on this car yet"); return false; }
    bool over = false;
    for (auto& x : g_saves) if (!_stricmp(x.name, nm)) { x = e; over = true; break; }
    if (!over) g_saves.push_back(e);
    if (!WriteSaves()) { ShowError("Could not write %s", SAVE_FILE); return false; }
    Status("saved '%s' (car id %d, %d textured parts)%s", nm, e.model, texCnt, over ? " - overwritten" : "");
    return true;
}

// ---- loading a save: the TXDs it needs are streamed in first (async), then everything is applied at once ----
struct LoadNeed {
    char name[24] = {0};
    int slot = -1;
    bool weLoaded = false, ready = false, bad = false, used = false;
    std::vector<RwTexture*> texs;
};
struct LoadJob {
    bool active = false;
    CVehicle* target = nullptr;
    DWORD t0 = 0;
    char name[32] = {0};
    std::vector<SavePart> parts;
    std::vector<LoadNeed> needs;
};
static LoadJob g_job;
static int g_reqIdx = -1;          // load request from the menu, started in Process
static bool g_reqSpawn = false;

static void CancelLoad() {
    if (!g_job.active) return;
    for (auto& n : g_job.needs) if (n.weLoaded && n.slot >= 0) UnreqTxd(n.slot);
    g_job = LoadJob();
}
static void FinishLoad() {
    for (auto& r : g_recs) { ReleaseAsg(r); r.on = r.autoOn; }
    for (auto& n : g_job.needs)
        if (n.ready && !n.bad) {
            RwTexDictionary* d = TxdGet(n.slot);
            if (!d || !EnumTex(d, &n.texs)) n.texs.clear();
        }
    int applied = 0, skipped = 0;
    for (auto& p : g_job.parts) {
        MatRec* r = nullptr;
        int seen = 0;
        for (auto& x : g_recs)
            if (!strcmp(x.frame, p.frame)) { if (seen++ == p.occ) { r = &x; break; } }
        if (!r || (p.on && !r->canUse)) { skipped++; continue; }
        r->on = p.on != 0;
        if (p.kind == 1) {
            LoadNeed* nd = nullptr;
            for (auto& n : g_job.needs) if (!_stricmp(n.name, p.txd)) { nd = &n; break; }
            RwTexture* t = nullptr;
            if (nd && nd->ready)
                for (RwTexture* c : nd->texs) if (c && !_stricmp(c->name, p.tex)) { t = c; break; }
            if (!t) { skipped++; continue; }
            AssignTexSlot(*r, t, nd->slot, nd->weLoaded, nd->name);
            nd->used = true;
            applied++;
        } else if (p.kind == 2) {
            if (p.design >= 0 && p.design < N_DESIGNS && AssignDesign(*r, p.design)) applied++; else skipped++;
        }
    }
    ApplyAll();
    for (auto& n : g_job.needs) if (n.weLoaded && !n.used && n.slot >= 0) UnreqTxd(n.slot);
    strncpy(g_loadedName, g_job.name, sizeof(g_loadedName) - 1);
    g_loadedName[sizeof(g_loadedName) - 1] = 0;
    if (skipped) Status("loaded '%s': %d parts, %d skipped (missing)", g_job.name, applied, skipped);
    else Status("loaded '%s': %d parts", g_job.name, applied);
    g_job = LoadJob();
}
static void PumpLoad() {
    if (!g_job.active) return;
    if (!g_veh || g_veh != g_job.target || !VehicleAlive(g_veh)) {
        CancelLoad();
        Status("load cancelled (car changed)");
        return;
    }
    DWORD now = GetTickCount();
    bool all = true;
    for (auto& n : g_job.needs) {
        if (n.ready || n.bad) continue;
        if (TxdGet(n.slot)) { n.ready = true; continue; }
        if (now - g_job.t0 > 8000) { n.bad = true; if (n.weLoaded) UnreqTxd(n.slot); continue; }
        all = false;
    }
    if (all) FinishLoad();
}

// spawning: the game's own vehicle cheat creates the car in front of the player (all vehicle classes)
static bool SpawnableModel(int m) {
#ifdef BT_HAVE_CCHEAT
    if (m < 400 || m > 611) return false;
    return !(m == 449 || m == 537 || m == 538 || m == 569 || m == 570 || m == 590);
#else
    (void)m;
    return false;
#endif
}
#ifdef BT_HAVE_CCHEAT
template<class R, class T> static void CallVehCheat(R (*fn)(T), int m) { fn((T)m); }
static bool SafeVehCheat(int model) {
    __try { CallVehCheat(&CCheat::VehicleCheat, model); return true; }
    __except (EXCEPTION_EXECUTE_HANDLER) { return false; }
}
#endif
static CVehicle* SpawnVehicleModel(int model) {
#ifdef BT_HAVE_CCHEAT
    auto pool = CPools::ms_pVehiclePool;
    if (!pool) return nullptr;
    std::vector<CVehicle*> before;
    for (int i = 0; i < pool->m_nSize; i++)
        if (!pool->IsFreeSlotAtIndex(i)) before.push_back(pool->GetAt(i));
    if (!SafeVehCheat(model)) return nullptr;
    CVehicle* found = nullptr;
    for (int i = 0; i < pool->m_nSize; i++) {
        if (pool->IsFreeSlotAtIndex(i)) continue;
        CVehicle* c = pool->GetAt(i);
        if (!c || c->m_nModelIndex != model) continue;
        if (std::find(before.begin(), before.end(), c) != before.end()) continue;
        found = c;
    }
    return found;
#else
    (void)model;
    return nullptr;
#endif
}
static void StartLoad(int si, bool spawn) {
    if (si < 0 || si >= (int)g_saves.size()) return;
    if (g_job.active) { ShowError("Still loading, wait a moment"); return; }
    if (!CTxdStore::ms_pTxdPool) return;
    const SaveEnt& s = g_saves[si];
    g_nSlots = CTxdStore::ms_pTxdPool->m_nSize;
    CVehicle* pv = FindPlayerVehicle(-1, false);
    CVehicle* target = nullptr;
    if (spawn) {
        if (pv) { ShowError("Get out of the car first, then press Spawn"); return; }
        if (!SpawnableModel(s.model)) { ShowError("This car cannot be spawned - sit in it and use Apply"); return; }
    } else {
        if (!pv) { ShowError("Sit in a car first to use Apply"); return; }
        if (pv->m_nModelIndex != s.model) {
            ShowError("This is not the car of this save (needs car id %d, you are in %d)", s.model, (int)pv->m_nModelIndex);
            return;
        }
        target = pv;
    }
    bool wasOff = (g_mode == 0);
    if (wasOff) g_mode = 1;
    if (spawn) {
        if (g_veh) Release();
        CVehicle* nv = SpawnVehicleModel(s.model);
        if (nv) Acquire(nv);
        if (!nv || g_veh != nv) {
            ShowError("Could not spawn this car");
            if (wasOff && !g_veh) g_mode = 0;
            return;
        }
        target = nv;
    } else if (g_veh != target) {
        if (g_veh) Release();
        Acquire(target);
        if (g_veh != target) {
            ShowError("Could not use this car");
            if (wasOff && !g_veh) g_mode = 0;
            return;
        }
    }
    g_job = LoadJob();
    g_job.active = true;
    g_job.target = target;
    g_job.t0 = GetTickCount();
    strncpy(g_job.name, s.name, sizeof(g_job.name) - 1);
    g_job.parts = s.parts;
    for (auto& p : g_job.parts) {
        if (p.kind != 1 || !p.txd[0]) continue;
        bool have = false;
        for (auto& n : g_job.needs) if (!_stricmp(n.name, p.txd)) { have = true; break; }
        if (have) continue;
        LoadNeed n;
        strncpy(n.name, p.txd, sizeof(n.name) - 1);
        int sl = FindSlotSafe(n.name);
        if (sl >= 0 && SlotValid(sl)) {
            n.slot = sl;
            if (TxdGet(sl)) n.ready = true;
            else { n.weLoaded = true; ReqTxd(sl); }
        } else n.bad = true;
        g_job.needs.push_back(n);
    }
    Status("loading '%s' ...", g_job.name);
    PumpLoad();
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
static bool g_focus = false;
static bool g_inHover = false;             // mouse is over the search field this frame
static char g_status[96] = "";
static unsigned g_statusT = 0;
static const float MOUSE_SENS = 1.0f;      // tune if cursor feels too slow/fast
static int  g_designPage = 0;             // page of the animated-design list in the menu
static bool g_glow = true;                 // light from the body into the world (F10 / menu button)
static bool g_invert = false;              // false = normal mouse, true = inverted (both axes); F9 or menu button
static bool g_saveTab = false;             // the "Save +" tab is shown
static bool g_naming = false;              // the name box of a new save is open
static char g_saveName[32] = "";
static int  g_savePage = 0;
static int  g_delArm = -1;                 // save that waits for the second click to be deleted
static unsigned g_delT = 0;
static char g_errMsg[128] = "";            // error bar that slides up from the bottom of the screen
static unsigned g_errT = 0;
static bool g_errOn = false;

static float SW() { return (float)RsGlobal.maximumWidth; }
static float SH() { return (float)RsGlobal.maximumHeight; }
static void Status(const char* fmt, ...) {
    va_list a; va_start(a, fmt);
    vsnprintf(g_status, sizeof(g_status), fmt, a);
    va_end(a);
    g_statusT = CTimer::m_snTimeInMilliseconds;
}
static void ShowError(const char* fmt, ...) {
    va_list a; va_start(a, fmt);
    vsnprintf(g_errMsg, sizeof(g_errMsg), fmt, a);
    va_end(a);
    g_errT = CTimer::m_snTimeInMilliseconds;
    g_errOn = true;
}

// ---------------- actions ----------------
static void SetMode(int m) {
    g_mode = m;
    if (m == 0) { if (g_veh) Release(); return; }
    if (m == 1) CatalogStart();
}
static void ToggleMenu() {
    g_menu = !g_menu;
    if (g_menu) {
        g_cx = SW() * 0.5f; g_cy = SH() * 0.5f;
        g_lmbPrev = true; g_focus = false;
        CatalogStart();
        if (!g_savesLoaded) LoadSaves();
    } else {
        g_focus = false;
        g_naming = false;
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
static bool TypeKeys(char* buf, int cap, bool keepCase) {
    size_t n = strlen(buf);
    bool changed = false;
    bool shift = (GetAsyncKeyState(VK_SHIFT) & 0x8000) != 0;
    for (int vk = 'A'; vk <= 'Z'; vk++)
        if (Pressed(vk) && (int)n < cap - 1) {
            char c = (char)(vk - 'A' + 'a');
            if (keepCase && shift) c = (char)(c - 32);
            buf[n++] = c; changed = true;
        }
    for (int vk = '0'; vk <= '9'; vk++)
        if (Pressed(vk) && (int)n < cap - 1) { buf[n++] = (char)vk; changed = true; }
    if (Pressed(VK_SPACE) && (int)n < cap - 1) { buf[n++] = ' '; changed = true; }
    if (Pressed(VK_OEM_MINUS) && (int)n < cap - 1) { buf[n++] = shift ? '_' : '-'; changed = true; }
    if (Pressed(VK_BACK) && n > 0) { n--; changed = true; }
    buf[n] = 0;
    return changed;
}
static void DoSaveName() {
    if (SaveCurrent(g_saveName)) { g_naming = false; g_saveName[0] = 0; }
}
static void HandleTyping() {
    if (g_naming) {
        TypeKeys(g_saveName, 28, true);
        if (Pressed(VK_RETURN)) DoSaveName();
        if (Pressed(VK_ESCAPE)) g_naming = false;
        return;
    }
    if (!g_focus) return;
    size_t n = strlen(g_search);
    bool changed = false;
    for (int vk = 'A'; vk <= 'Z'; vk++)
        if (Pressed(vk) && n < 30) { g_search[n++] = (char)(vk - 'A' + 'a'); changed = true; }
    for (int vk = '0'; vk <= '9'; vk++)
        if (Pressed(vk) && n < 30) { g_search[n++] = (char)vk; changed = true; }
    if (Pressed(VK_SPACE) && n < 30) { g_search[n++] = ' '; changed = true; }
    if (Pressed(VK_OEM_MINUS) && n < 30) { g_search[n++] = (GetAsyncKeyState(VK_SHIFT) & 0x8000) ? '_' : '-'; changed = true; }
    if (Pressed(VK_BACK) && n > 0) { n--; changed = true; }
    g_search[n] = 0;
    if (changed) g_dirty = true;
    if (Pressed(VK_RETURN)) GoSearch();
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
static bool ButtonS(const char* label, float x, float y, float w, float h, bool selected, float ts) {
    bool hov = Hover(x, y, w, h);
    CRGBA bg = selected ? CRGBA(30, 24, 8, 242) : (hov ? CRGBA(28, 23, 10, 242) : CRGBA(12, 12, 14, 232));
    FillRect(x, y, w, h, bg);
    if (selected) FillRect(x, y, w, h * 0.5f, CRGBA(212, 175, 55, 34));
    GoldBorder(x, y, w, h, 1.0f, (selected || hov) ? C_GOLD_LT : C_GOLD_DK);
    if (selected || hov) RgbLine(x + 2, y + h - 3.0f, w - 4, 1.6f);
    if (selected) FillRect(x, y, 3.0f, h, C_GOLD);
    CRGBA tc = selected ? C_GOLD_LT : (hov ? CRGBA(255, 255, 255, 255) : CRGBA(222, 222, 226, 255));
    Text(x + 8, y + h * 0.18f, label, tc, ts);
    return hov && g_click;
}
static bool Button(const char* label, float x, float y, float w, float h, bool selected) {
    return ButtonS(label, x, y, w, h, selected, 0.85f);
}
// small button for the rows of the parts list
static void MiniBtn(const char* label, float x, float y, float w, float h, bool hov) {
    FillRect(x, y, w, h, hov ? CRGBA(70, 55, 16, 245) : CRGBA(22, 20, 12, 235));
    GoldBorder(x, y, w, h, 1.0f, hov ? C_GOLD_LT : C_GOLD_DK);
    Text(x + w * 0.5f - (float)strlen(label) * SW() * 0.0033f, y + h * 0.1f, label, hov ? CRGBA(255, 255, 255, 255) : C_GOLD_LT, 0.65f);
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

// right-hand panel: every part/material found on the car. Checkbox = part is active, "Set" = put the current
// selection on this part only, "x" = remove its texture. "Apply to all parts" paints every active part.
static void DrawParts(float px, float py, float pw, float ph) {
    if (g_recs.empty() || !g_veh || g_mode == 0) return;
    float W = SW(), H = SH();
    float x0 = px + pw + 10.0f;
    float w0 = W - x0 - 10.0f;
    if (w0 < 80.0f) return;
    float pad = 10.0f, gap = 6.0f, bh = H * 0.045f, rowH = H * 0.036f;
    Panel(x0, py, w0, ph, false);
    int total = (int)g_recs.size(), onCnt = 0, texCnt = 0;
    for (auto& r : g_recs) { if (r.on) onCnt++; if (r.on && r.asgKind) texCnt++; }
    char head[96];
    sprintf(head, "Parts  %d/%d on | %d textured", onCnt, total, texCnt);
    Text(x0 + pad, py + 8, head, C_GOLD_LT, 0.8f);
    FillRect(x0 + pad, py + H * 0.05f, w0 - 2 * pad, 1.0f, C_GOLD_DK);
    float y = py + H * 0.062f;
    float y3 = py + ph - bh - pad;      // All on / Reset / Clear
    float y2 = y3 - bh - gap;           // page buttons
    float y1 = y2 - bh - gap;           // apply to all parts
    float listBottom = y1 - gap;
    int perPage = (int)((listBottom - y) / rowH);
    if (perPage < 1) perPage = 1;
    int pages = (total + perPage - 1) / perPage;
    if (g_partPage >= pages) g_partPage = pages - 1;
    if (g_partPage < 0) g_partPage = 0;
    float rx = x0 + pad, rw = w0 - 2 * pad;
    float clrW = rowH * 0.95f, setW = rowH * 1.7f;
    float clrX = rx + rw - clrW - 2.0f, setX = clrX - setW - 3.0f;
    float cw = W * 0.0072f;             // approximate glyph width at text scale 0.7
    for (int i = g_partPage * perPage; i < total && i < (g_partPage + 1) * perPage; i++) {
        MatRec& r = g_recs[i];
        bool hov = Hover(rx, y, rw, rowH - 2);
        bool hovSet = r.canUse && Hover(setX, y + 1, setW, rowH - 4);
        bool hovClr = r.canUse && Hover(clrX, y + 1, clrW, rowH - 4);
        bool hovRow = hov && !hovSet && !hovClr;
        if (hovRow) { FillRect(rx, y, rw, rowH - 2, CRGBA(212, 175, 55, 30)); FillRect(rx, y, 2.0f, rowH - 2, C_GOLD); }
        float s = rowH * 0.34f, sy = y + (rowH - 2 - s) * 0.5f;
        if (r.on) FillRect(rx + 6, sy, s, s, C_GOLD_LT);
        else GoldBorder(rx + 6, sy, s, s, 1.0f, C_GOLD_DK);
        float tx = rx + 6 + s + 8;
        float avail = (r.canUse ? setX : rx + rw) - tx - 4.0f;
        int maxc = (int)(avail / cw);
        if (maxc < 6) maxc = 6;
        if (maxc > 60) maxc = 60;
        char line[160];
        CRGBA tc;
        if (r.on) {
            const char* an = "-";
            if (r.asgKind == 1 && r.asgTex) an = r.asgTex->name;
            else if (r.asgKind == 2) an = DESIGN_NAME[r.asgDesign];
            int fc = maxc * 55 / 100; if (fc < 4) fc = 4;
            int ac = maxc - fc - 3; if (ac < 0) ac = 0;
            snprintf(line, sizeof(line), "%.*s > %.*s", fc, r.frame, ac, an);
            tc = r.asgKind ? C_GOLD_LT : CRGBA(205, 190, 130, 255);
        } else {
            int fc = maxc - 7; if (fc < 4) fc = 4;
            snprintf(line, sizeof(line), "%.*s (%s)", fc, r.frame, r.why[0] ? r.why : "off");
            tc = CRGBA(150, 150, 156, 255);
        }
        Text(tx, y + 1, line, tc, 0.7f);
        if (r.canUse) {
            MiniBtn("Set", setX, y + 1, setW, rowH - 4, hovSet);
            MiniBtn("x", clrX, y + 1, clrW, rowH - 4, hovClr);
        }
        if (g_click) {
            if (hovSet) {
                if (!SelValid()) Status("select a texture / design first");
                else { r.on = true; if (AssignSel(r)) ApplyPart(r); }
            } else if (hovClr) {
                ReleaseAsg(r); ApplyPart(r);
            } else if (hovRow && r.canUse) {
                r.on = !r.on; ApplyPart(r);
            }
        }
        y += rowH;
    }
    if (Button("Apply to all parts", rx, y1, rw, bh, false)) ApplySelToAll();
    float bw2 = (rw - gap) / 2;
    if (Button("< Page", rx, y2, bw2, bh, false)) g_partPage--;
    if (Button("Page >", rx + bw2 + gap, y2, bw2, bh, false)) g_partPage++;
    float bw3 = (rw - 2 * gap) / 3;
    if (ButtonS("All on", rx, y3, bw3, bh, false, 0.7f)) { for (auto& r : g_recs) if (r.canUse) r.on = true; ApplyAll(); }
    if (ButtonS("Reset", rx + bw3 + gap, y3, bw3, bh, false, 0.7f)) { for (auto& r : g_recs) r.on = r.autoOn; ApplyAll(); }
    if (ButtonS("Clear", rx + 2 * (bw3 + gap), y3, bw3, bh, false, 0.7f)) {
        for (auto& r : g_recs) ReleaseAsg(r);
        ApplyAll();
        Status("all part textures removed");
    }
}

// category 1 browser: categories + search + paged list of TXDs (or single textures), then the textures of one TXD
static void DrawPageNav(float x, float y, float w, float h, float gap, int& page, int pages, int jump) {
    float sm = w * 0.12f;
    float mid = w - 4 * sm - 4 * gap;
    if (ButtonS("<<", x, y, sm, h, false, 0.7f)) page = (page + pages - jump % pages) % pages;
    if (ButtonS("<", x + sm + gap, y, sm, h, false, 0.7f)) page = (page + pages - 1) % pages;
    char pg[40];
    sprintf(pg, "Page %d / %d", page + 1, pages);
    float mx = x + 2 * (sm + gap);
    GoldBorder(mx, y, mid, h, 1.0f, C_GOLD_DK);
    Text(mx + 8, y + h * 0.18f, pg, C_GOLD_LT, 0.7f);
    if (ButtonS(">", mx + mid + gap, y, sm, h, false, 0.7f)) page = (page + 1) % pages;
    if (ButtonS(">>", mx + mid + gap + sm + gap, y, sm, h, false, 0.7f)) page = (page + jump) % pages;
}
static void DrawBrowser(float px, float pw, float y, float bottom, float pad, float gap) {
    float W = SW(), H = SH();
    float smallH = H * 0.04f, rowH = H * 0.032f, inH = H * 0.045f;
    float cw = W * 0.0077f;   // approximate glyph width at text scale 0.75
    if (g_dirty) RebuildList();

    char info[160];
    RwTexture* ct = CurTex();
    if (g_pendSlot >= 0) sprintf(info, "Loading '%s' ...", g_openName);
    else if (g_opened) sprintf(info, "TXD %s | %s (%d/%d)", g_openName, ct ? ct->name : "-", g_idx + 1, (int)g_tex.size());
    else strcpy(info, "Pick a TXD below, or type its name and press Go");
    Text(px + pad, y, info, C_TXT, 0.8f);
    y += H * 0.04f;

    float navY = bottom - smallH;

    if (g_view == 0) {
        // ---- category chips ----
        const int perRow = 6;
        float chipW = (pw - 2 * pad - (perRow - 1) * gap) / perRow;
        float rg = gap * 0.6f;
        for (int c = 0; c < N_TC; c++) {
            int rr = c / perRow, cc = c % perRow;
            if (ButtonS(TC_NAME[c], px + pad + cc * (chipW + gap), y + rr * (smallH + rg), chipW, smallH, g_cat == c, 0.7f)) {
                g_cat = c; g_dirty = true;
            }
        }
        y += 2 * smallH + rg + gap;

        // ---- search row ----
        float inW = pw * 0.44f, goW = pw * 0.12f;
        float tgW = pw - 2 * pad - inW - goW - 2 * gap;
        g_inHover = Hover(px + pad, y, inW, inH);
        if (g_inHover && g_click) g_focus = true;
        FillRect(px + pad, y, inW, inH, CRGBA(0, 0, 0, 240));
        if (g_focus) RgbBorder(px + pad, y, inW, inH, 2.2f); else GoldBorder(px + pad, y, inW, inH, 1.0f, C_GOLD_DK);
        bool blink = ((CTimer::m_snTimeInMilliseconds / 500) & 1) != 0;
        if (!g_search[0] && !g_focus) {
            Text(px + pad + 8, y + inH * 0.2f, "search...", CRGBA(120, 120, 126, 255), 0.8f);
        } else {
            char shown[48];
            sprintf(shown, "%s%s", g_search, (g_focus && blink) ? "_" : "");
            Text(px + pad + 8, y + inH * 0.2f, shown, CRGBA(255, 255, 255, 255), 0.8f);
        }
        if (ButtonS("Go", px + pad + inW + gap, y, goW, inH, false, 0.8f)) GoSearch();
        if (ButtonS(g_texMode ? "Show: Textures" : "Show: TXDs", px + pad + inW + goW + 2 * gap, y, tgW, inH, g_texMode, 0.7f)) {
            g_texMode = !g_texMode; g_dirty = true;
        }
        y += inH + gap;

        // ---- result line ----
        int st = g_stage.load();
        int total = g_scanTotal.load();
        int pct = total > 0 ? (int)((long long)g_scanDone.load() * 100 / total) : 0;
        char rl[140];
        if (st == 0) strcpy(rl, "Starting the game texture index ...");
        else if (!g_resolved) strcpy(rl, "Matching TXDs with this game ...");
        else if (st < 2 && g_texMode) sprintf(rl, "Indexing texture names %d%% ... (TXD list works meanwhile)", pct);
        else if (st < 2) sprintf(rl, "%d TXDs | texture-name search ready in %d%%", (int)g_list.size(), pct);
        else sprintf(rl, "%d %s | %s", (int)g_list.size(), g_texMode ? "textures" : "TXDs", TC_FULL[g_cat]);
        Text(px + pad, y, rl, C_GOLD_LT, 0.7f);
        y += H * 0.032f;

        // ---- paged list, two columns ----
        float listTop = y, listBottom = navY - gap;
        int rowsPerCol = (int)((listBottom - listTop) / rowH);
        if (rowsPerCol < 1) rowsPerCol = 1;
        int perPage = rowsPerCol * 2;
        int count = (int)g_list.size();
        int pages = (count + perPage - 1) / perPage;
        if (pages < 1) pages = 1;
        if (g_listPage >= pages) g_listPage = pages - 1;
        if (g_listPage < 0) g_listPage = 0;
        float colW = (pw - 2 * pad - gap) / 2;
        int maxc = (int)((colW - 12.0f) / cw);
        if (maxc < 8) maxc = 8;
        if (maxc > 40) maxc = 40;
        for (int k = 0; k < perPage; k++) {
            int li = g_listPage * perPage + k;
            if (li >= count) break;
            int col = k / rowsPerCol, row = k % rowsPerCol;
            float rx = px + pad + col * (colW + gap), ry = listTop + row * rowH;
            bool hov = Hover(rx, ry, colW, rowH - 2);
            char line[96];
            bool current;
            if (!g_texMode) {
                int ti = g_list[li];
                current = g_opened && ti == g_openIdx;
                if (st >= 2 && ti < (int)g_txdCount.size()) snprintf(line, sizeof(line), "%.*s (%d)", maxc - 5 > 8 ? maxc - 5 : 8, g_txds[ti].name, g_txdCount[ti]);
                else snprintf(line, sizeof(line), "%.*s", maxc, g_txds[ti].name);
            } else {
                const TexEnt& te = g_texs[g_list[li]];
                current = false;
                int a = maxc * 55 / 100; if (a < 6) a = 6;
                int b = maxc - a - 3; if (b < 3) b = 3;
                snprintf(line, sizeof(line), "%.*s  %.*s", a, te.name, b, g_txds[te.txd].name);
            }
            if (current) FillRect(rx, ry, colW, rowH - 2, CRGBA(212, 175, 55, 46));
            if (hov) { FillRect(rx, ry, colW, rowH - 2, CRGBA(212, 175, 55, 34)); FillRect(rx, ry, 2.0f, rowH - 2, C_GOLD); }
            Text(rx + 6, ry + 1, line, (hov || current) ? C_GOLD_LT : CRGBA(222, 222, 226, 255), 0.75f);
            if (hov && g_click) {
                if (!g_texMode) OpenTxdIdx(g_list[li], 0);
                else {
                    const TexEnt& te = g_texs[g_list[li]];
                    BeginOpen(g_txds[te.txd].slot, te.txd, g_txds[te.txd].name, te.name, 0);
                }
            }
        }
        int jump = pages / 10; if (jump < 5) jump = 5;
        DrawPageNav(px + pad, navY, pw - 2 * pad, smallH, gap, g_listPage, pages, jump);
    } else {
        // ---- textures of the opened TXD ----
        float bw5 = (pw - 2 * pad - 4 * gap) / 5;
        if (ButtonS("< Back", px + pad, y, bw5, smallH, false, 0.7f)) g_view = 0;
        if (ButtonS("<< TXD", px + pad + (bw5 + gap), y, bw5, smallH, false, 0.7f)) { int i = NextTxd(-1); if (i >= 0) OpenTxdIdx(i, 0); }
        if (ButtonS("TXD >>", px + pad + 2 * (bw5 + gap), y, bw5, smallH, false, 0.7f)) { int i = NextTxd(1); if (i >= 0) OpenTxdIdx(i, 0); }
        if (ButtonS("< Tex", px + pad + 3 * (bw5 + gap), y, bw5, smallH, false, 0.7f)) { if (g_opened && g_idx > 0) { g_idx--; g_texJump = true; } }
        if (ButtonS("Tex >", px + pad + 4 * (bw5 + gap), y, bw5, smallH, false, 0.7f)) { if (g_opened && g_idx + 1 < (int)g_tex.size()) { g_idx++; g_texJump = true; } }
        y += smallH + gap;

        float listW = (pw - 2 * pad - gap) * 0.55f;
        float rightX = px + pad + listW + gap, rightW = pw - 2 * pad - listW - gap;
        float listTop = y, listBottom = navY - gap;
        int rows = (int)((listBottom - listTop) / rowH);
        if (rows < 1) rows = 1;
        int count = (int)g_tex.size();
        int pages = (count + rows - 1) / rows;
        if (pages < 1) pages = 1;
        if (g_texJump) { if (g_idx >= 0) g_texPage = g_idx / rows; g_texJump = false; }
        if (g_texPage >= pages) g_texPage = pages - 1;
        if (g_texPage < 0) g_texPage = 0;
        RwTexture* hoverTex = nullptr;
        int maxc = (int)((listW - 12.0f) / cw);
        if (maxc < 8) maxc = 8;
        if (maxc > 31) maxc = 31;
        if (g_pendSlot >= 0) {
            Text(px + pad + 6, listTop + 4, "Loading the TXD ...", C_TXT, 0.8f);
        } else if (count == 0) {
            Text(px + pad + 6, listTop + 4, "No textures here. Press < Back.", C_TXT, 0.8f);
        }
        for (int k = 0; k < rows; k++) {
            int ti = g_texPage * rows + k;
            if (ti >= count || g_pendSlot >= 0) break;
            RwTexture* tx = g_tex[ti];
            float ry = listTop + k * rowH;
            bool hov = Hover(px + pad, ry, listW, rowH - 2);
            bool sel = (ti == g_idx);
            if (sel) { FillRect(px + pad, ry, listW, rowH - 2, CRGBA(212, 175, 55, 52)); FillRect(px + pad, ry, 3.0f, rowH - 2, C_GOLD); }
            if (hov) { FillRect(px + pad, ry, listW, rowH - 2, CRGBA(212, 175, 55, 30)); hoverTex = tx; }
            char line[48];
            snprintf(line, sizeof(line), "%.*s", maxc, tx->name);
            Text(px + pad + 8, ry + 1, line, (sel || hov) ? C_GOLD_LT : CRGBA(222, 222, 226, 255), 0.75f);
            if (hov && g_click) { g_idx = ti; Status("selected %s - press Apply to all parts, or Set on one part", tx->name); }
        }
        DrawPageNav(px + pad, navY, listW, smallH, gap * 0.5f, g_texPage, pages, 5);

        // preview of the hovered (or selected) texture
        RwTexture* pv = hoverTex ? hoverTex : CurTex();
        float s = rightW;
        float maxS = (listBottom - listTop) - H * 0.12f;
        if (s > maxS) s = maxS;
        if (s < 40.0f) s = 40.0f;
        FillRect(rightX, listTop, s, s, CRGBA(0, 0, 0, 255));
        if (pv && g_pendSlot < 0) {
            CSprite2d spr;
            spr.m_pTexture = pv;
            spr.Draw(CRect(rightX + 2, listTop + s - 2, rightX + s - 2, listTop + 2), CRGBA(255, 255, 255, 255));
            spr.m_pTexture = nullptr;   // the texture belongs to the TXD, the sprite must not free it
        }
        GoldBorder(rightX, listTop, s, s, 1.0f, C_GOLD);
        char nm[48];
        snprintf(nm, sizeof(nm), "%.28s", pv ? pv->name : "-");
        Text(rightX, listTop + s + 4, nm, C_GOLD_LT, 0.75f);
        Text(rightX, listTop + s + 4 + H * 0.034f, "click = select", CRGBA(170, 170, 176, 255), 0.65f);
        Text(rightX, listTop + s + 4 + H * 0.058f, "then Apply / Set", CRGBA(170, 170, 176, 255), 0.65f);
    }
}

// error bar: slides up from the bottom edge of the screen
static void DrawErrBanner() {
    if (!g_errOn) return;
    unsigned el = CTimer::m_snTimeInMilliseconds - g_errT;
    const unsigned SHOWMS = 4200;
    if (el > SHOWMS) { g_errOn = false; return; }
    float W = SW(), H = SH();
    float bh = H * 0.07f;
    float k = 1.0f;
    if (el < 260) k = el / 260.0f;
    else if (el > SHOWMS - 300) k = (SHOWMS - el) / 300.0f;
    k = 1.0f - (1.0f - k) * (1.0f - k);
    float y = H - bh * k;
    FillRect(0, y, W, bh + 2.0f, CRGBA(26, 4, 4, 240));
    FillRect(0, y, W, 2.5f, CRGBA(255, 70, 70, 255));
    float tw = (float)strlen(g_errMsg) * W * 0.0085f;
    float x = (W - tw) * 0.5f;
    if (x < 10.0f) x = 10.0f;
    Text(x, y + bh * 0.24f, g_errMsg, CRGBA(255, 215, 215, 255), 0.9f);
}
static bool ButtonOff(const char* label, float x, float y, float w, float h, float ts, bool enabled, const char* offMsg) {
    if (enabled) return ButtonS(label, x, y, w, h, false, ts);
    FillRect(x, y, w, h, CRGBA(10, 10, 12, 220));
    GoldBorder(x, y, w, h, 1.0f, CRGBA(70, 62, 40, 255));
    Text(x + 8, y + h * 0.18f, label, CRGBA(95, 95, 100, 255), ts);
    if (Hover(x, y, w, h) && g_click) Status("%s", offMsg);
    return false;
}
// "Save +" tab: + opens a name box, below it the list of saves with Spawn / Apply / Del
static void DrawSaves(float px, float pw, float y, float bottom, float pad, float gap) {
    float W = SW(), H = SH();
    float smallH = H * 0.04f, bh = H * 0.055f, rowH = H * 0.05f, lineH = H * 0.03f;
    unsigned now = CTimer::m_snTimeInMilliseconds;
    if (!g_savesLoaded) LoadSaves();
    bool inCar = FindPlayerVehicle(-1, false) != nullptr;
    float rw = pw - 2 * pad;
    CRGBA gray(150, 150, 156, 255);

    // ---- "+" and the name box ----
    float plus = bh;
    if (g_naming) {
        ButtonS("", px + pad, y, plus, bh, true, 0.8f);
        Text(px + pad + plus * 0.5f - W * 0.0055f, y + bh * 0.06f, "+", C_GOLD_LT, 1.5f);
        float okW = pw * 0.13f, noW = pw * 0.16f;
        float inX = px + pad + plus + gap, inW = rw - plus - okW - noW - 3 * gap;
        FillRect(inX, y, inW, bh, CRGBA(0, 0, 0, 240));
        RgbBorder(inX, y, inW, bh, 2.2f);
        bool blink = ((now / 500) & 1) != 0;
        if (!g_saveName[0]) {
            Text(inX + 8, y + bh * 0.22f, blink ? "type a name_" : "type a name", CRGBA(120, 120, 126, 255), 0.8f);
        } else {
            char shown[48];
            sprintf(shown, "%s%s", g_saveName, blink ? "_" : "");
            Text(inX + 8, y + bh * 0.22f, shown, CRGBA(255, 255, 255, 255), 0.85f);
        }
        if (ButtonS("Save", inX + inW + gap, y, okW, bh, false, 0.8f)) DoSaveName();
        if (ButtonS("Cancel", inX + inW + okW + 2 * gap, y, noW, bh, false, 0.75f)) g_naming = false;
    } else {
        if (ButtonS("", px + pad, y, plus, bh, false, 0.8f)) {
            if (!g_veh || g_mode == 0) ShowError("Get into a car and paint it first");
            else { g_naming = true; g_saveName[0] = 0; g_focus = false; }
        }
        Text(px + pad + plus * 0.5f - W * 0.0055f, y + bh * 0.06f, "+", C_GOLD_LT, 1.5f);
        Text(px + pad + plus + gap + 4, y + bh * 0.24f, "New save of the current car (+)", C_GOLD_LT, 0.8f);
    }
    y += bh + gap;

    // ---- list ----
    float navY = bottom - smallH;
    float hintY = navY - gap - 2 * lineH;
    float listTop = y, listBottom = hintY - gap * 0.5f;
    int perPage = (int)((listBottom - listTop) / rowH);
    if (perPage < 1) perPage = 1;
    int total = (int)g_saves.size();
    int pages = (total + perPage - 1) / perPage;
    if (pages < 1) pages = 1;
    if (g_savePage >= pages) g_savePage = pages - 1;
    if (g_savePage < 0) g_savePage = 0;
    if (total == 0) Text(px + pad + 4, listTop + 6, "No saves yet. Paint a car, then tap + and name it.", C_TXT, 0.75f);

    int actLoad = -1, actDel = -1;
    bool actSpawn = false;
    float delW = rowH * 1.5f, apW = rw * 0.15f, spW = rw * 0.16f;
    float delX = px + pad + rw - delW, apX = delX - 4.0f - apW, spX = apX - 4.0f - spW;
    float cw = W * 0.0072f;
    for (int i = g_savePage * perPage; i < total && i < (g_savePage + 1) * perPage; i++) {
        const SaveEnt& e = g_saves[i];
        float ry = listTop + (i - g_savePage * perPage) * rowH;
        bool hov = Hover(px + pad, ry, rw, rowH - 3);
        FillRect(px + pad, ry, rw, rowH - 3, hov ? CRGBA(212, 175, 55, 30) : CRGBA(255, 255, 255, 8));
        if (hov) FillRect(px + pad, ry, 2.0f, rowH - 3, C_GOLD);
        int tcnt = 0;
        for (auto& p : e.parts) if (p.kind) tcnt++;
        char tail[48];
        snprintf(tail, sizeof(tail), "  [id %d | %d parts]", e.model, tcnt);
        int maxc = (int)((spX - (px + pad) - 14.0f) / cw);
        int nc = maxc - (int)strlen(tail);
        if (nc < 4) nc = 4;
        char line[128];
        snprintf(line, sizeof(line), "%.*s%s", nc, e.name, tail);
        Text(px + pad + 8, ry + rowH * 0.2f, line, hov ? C_GOLD_LT : CRGBA(222, 222, 226, 255), 0.75f);
        float by = ry + 1.0f, bhh = rowH - 5.0f;
        if (ButtonS("Spawn", spX, by, spW, bhh, false, 0.65f)) { actLoad = i; actSpawn = true; }
        if (ButtonOff("Apply", apX, by, apW, bhh, 0.65f, inCar, "Sit in a car to use Apply")) { actLoad = i; actSpawn = false; }
        bool armed = (g_delArm == i && now - g_delT < 3000);
        if (ButtonS(armed ? "Sure?" : "Del", delX, by, delW, bhh, armed, 0.65f)) {
            if (armed) actDel = i; else { g_delArm = i; g_delT = now; }
        }
    }
    DrawPageNav(px + pad, navY, rw, smallH, gap * 0.5f, g_savePage, pages, 3);
    Text(px + pad, hintY, "Spawn = the car appears with this save (be on foot)", gray, 0.62f);
    Text(px + pad, hintY + lineH, "Apply = onto the car you sit in (same car id only)", gray, 0.62f);

    if (actDel >= 0) {
        char nm[32]; strncpy(nm, g_saves[actDel].name, 31); nm[31] = 0;
        g_saves.erase(g_saves.begin() + actDel);
        g_delArm = -1;
        WriteSaves();
        Status("deleted '%s'", nm);
    } else if (actLoad >= 0) {
        g_reqIdx = actLoad; g_reqSpawn = actSpawn;
    }
}

static void DrawMenu() {
    static bool logged = false;
    if (!logged) { logged = true; Log("menu drawn"); }
    float W = SW(), H = SH();
    float pw = W * 0.48f, ph = H * (g_saveTab ? 0.86f : ((g_mode == 1 || g_mode == 2) ? 0.90f : 0.74f)), px = (W - pw) * 0.5f, py = (H - ph) * 0.5f;
    float pad = 14.0f, gap = 8.0f, bh = H * 0.058f, hh = H * 0.115f;
    Panel(px, py, pw, ph, true);
    DrawHeader(px, py, pw, hh, pad);

    float y = py + hh + H * 0.02f;
    float bw3 = (pw - 2 * pad - 2 * gap) / 3;
    float bw4 = (pw - 2 * pad - 3 * gap) / 4;
    if (ButtonS("Off", px + pad, y, bw4, bh, !g_saveTab && g_mode == 0, 0.75f)) { g_saveTab = false; g_naming = false; SetMode(0); }
    if (ButtonS("1: Textures", px + pad + (bw4 + gap), y, bw4, bh, !g_saveTab && g_mode == 1, 0.75f)) { g_saveTab = false; g_naming = false; SetMode(1); }
    if (ButtonS("2: Animated", px + pad + 2 * (bw4 + gap), y, bw4, bh, !g_saveTab && g_mode == 2, 0.75f)) { g_saveTab = false; g_naming = false; SetMode(2); }
    if (ButtonS("Save  +", px + pad + 3 * (bw4 + gap), y, bw4, bh, g_saveTab, 0.75f)) { g_saveTab = true; g_focus = false; }
    y += bh + H * (((g_mode == 1 || g_mode == 2) && !g_saveTab) ? 0.012f : 0.03f);

    unsigned now = CTimer::m_snTimeInMilliseconds;
    float fy = py + ph - bh - pad;
    g_inHover = false;

    if (g_saveTab) {
        DrawSaves(px, pw, y, fy - H * 0.045f, pad, gap);
    } else if (g_mode == 1) {
        DrawBrowser(px, pw, y, fy - H * 0.045f, pad, gap);
    } else if (g_mode == 2) {
        Text(px + pad, y, "Pick a category and a design, then Apply to all parts (or Set on one part)", C_TXT, 0.68f);
        y += H * 0.032f;
        char sel[96];
        sprintf(sel, "Selected: %s", DESIGN_NAME[g_design]);
        Text(px + pad, y, sel, C_GOLD_LT, 0.85f);
        y += H * 0.04f;
        static int lastD = -1;
        if (g_design != lastD) { g_designCat = DesignCatOf(g_design); lastD = g_design; }
        // category buttons: 4 per row
        float cbw = (pw - 2 * pad - 3 * gap) / 4, cbh = H * 0.04f;
        for (int c = 0; c < N_DC; c++)
            if (ButtonS(DCATS[c].name, px + pad + (c % 4) * (cbw + gap), y + (c / 4) * (cbh + gap * 0.6f), cbw, cbh, g_designCat == c, 0.66f)) {
                g_designCat = c; g_designPage = 0;
            }
        y += 2 * cbh + gap * 0.6f + gap;
        // design list (left) + live preview (right)
        const DesignCat& dc = DCATS[g_designCat];
        float rightW = (pw - 2 * pad) * 0.36f, listW = pw - 2 * pad - rightW - gap;
        float rowH = H * 0.037f, navH = H * 0.04f, bottom = fy - H * 0.045f;
        int rows = (int)((bottom - y - navH - gap) / (rowH + 3.0f));
        if (rows < 3) rows = 3; if (rows > 8) rows = 8;
        int pages = (dc.n + rows - 1) / rows;
        if (g_designPage >= pages) g_designPage = pages - 1;
        if (g_designPage < 0) g_designPage = 0;
        int hoverId = -1;
        for (int j = 0; j < rows; j++) {
            int i = g_designPage * rows + j;
            if (i >= dc.n) break;
            int id = dc.ids[i];
            float ry = y + j * (rowH + 3.0f);
            if (Hover(px + pad, ry, listW, rowH)) hoverId = id;
            if (ButtonS(DESIGN_NAME[id], px + pad, ry, listW, rowH, g_design == id, 0.74f))
                g_design = id;     // only selects; it goes on the car with "Apply to all parts" / "Set"
        }
        float navY = y + rows * (rowH + 3.0f) + gap * 0.5f;
        if (pages > 1) {
            float nw = (listW - 2 * gap) / 3;
            if (Button("< Prev", px + pad, navY, nw, navH, false)) g_designPage = (g_designPage + pages - 1) % pages;
            char pg[32];
            sprintf(pg, "Page %d / %d", g_designPage + 1, pages);
            GoldBorder(px + pad + nw + gap, navY, nw, navH, 1.0f, C_GOLD_DK);
            Text(px + pad + nw + gap + 10, navY + navH * 0.18f, pg, C_GOLD_LT, 0.7f);
            if (Button("Next >", px + pad + 2 * (nw + gap), navY, nw, navH, false)) g_designPage = (g_designPage + 1) % pages;
        }
        // live preview of the hovered (or selected) design
        int pvId = hoverId >= 0 ? hoverId : g_design;
        float pxl = px + pad + listW + gap;
        float s = rightW;
        float maxS = rows * (rowH + 3.0f) + navH * 0.5f;
        if (s > maxS) s = maxS;
        FillRect(pxl, y, s, s, CRGBA(0, 0, 0, 255));
        RwTexture* ptx = PreviewTex(pvId);
        if (ptx) {
            CSprite2d spr;
            spr.m_pTexture = ptx;
            spr.Draw(CRect(pxl + 2, y + s - 2, pxl + s - 2, y + 2), CRGBA(255, 255, 255, 255));
            spr.m_pTexture = nullptr;   // the texture is ours, the sprite must not free it
        }
        GoldBorder(pxl, y, s, s, 1.0f, C_GOLD);
        char nm[48];
        snprintf(nm, sizeof(nm), "%.26s", DESIGN_NAME[pvId]);
        Text(pxl, y + s + 4, nm, C_GOLD_LT, 0.7f);
        Text(pxl, y + s + 4 + H * 0.03f, "live preview", CRGBA(170, 170, 176, 255), 0.62f);
    } else {
        Text(px + pad, y, "Choose a category above. Get into a car to see the result.", C_TXT, 0.85f);
    }
    // clicking anywhere except the text field removes focus
    if (g_click && !g_inHover) g_focus = false;

    // status line + bottom row (mouse mode, close)
    if (g_status[0] && now - g_statusT < 6000)
        Text(px + pad, fy - H * 0.04f, g_status, C_GOLD_LT, 0.8f);
    else if (!g_veh && g_mode != 0)
        Text(px + pad, fy - H * 0.04f, "Get into a car to apply.", C_GOLD_LT, 0.85f);
    if (Button(g_invert ? "Mouse: Inverted" : "Mouse: Normal", px + pad, fy, bw3, bh, g_invert)) {
        g_invert = !g_invert;
        Status(g_invert ? "mouse inverted (F9 toggles)" : "mouse normal (F9 toggles)");
    }
    if ((g_mode == 2 || g_saveTab) && Button(g_glow ? "Glow light: On" : "Glow light: Off", px + pad + bw3 + gap, fy, bw3, bh, g_glow)) {
        g_glow = !g_glow;
        Status(g_glow ? "glow light on (F10 toggles)" : "glow light off (F10 toggles)");
    }
    if (Button("Close  (type PRS)", px + pw - pad - bw3, fy, bw3, bh, false)) ToggleMenu();

    DrawParts(px, py, pw, ph);

    DrawErrBanner();

    // cursor: gold cross with black outline and its own RGB ring
    FillRect(g_cx - 2, g_cy - 10, 4, 20, CRGBA(0, 0, 0, 255));
    FillRect(g_cx - 10, g_cy - 2, 20, 4, CRGBA(0, 0, 0, 255));
    FillRect(g_cx - 1, g_cy - 9, 2, 18, C_GOLD_LT);
    FillRect(g_cx - 9, g_cy - 1, 18, 2, C_GOLD_LT);
    RgbBorder(g_cx - 6, g_cy - 6, 12, 12, 1.5f);
    g_click = false;
}

// light that streams out of the body into the game world; its colour follows the animated designs in use
static void AddGlowLights() {
    if (!g_veh || !g_glow) return;
    float t = CTimer::m_snTimeInMilliseconds / 1000.0f;
    float ar = 0, ag = 0, ab = 0;
    int used = 0;
    for (auto& d : g_dyns) {
        if (!DesignIsGlow(d.design) || !DesignInUse(d.design)) continue;
        int ns = (MatVariant(d.design) >= 0) ? 8 : 4;      // matrix text is sparse: sample more points
        for (int i = 0; i < ns * ns; i++) {
            uint32_t c = Pixel(d.design, ((i % ns) + 0.5f) / ns, ((i / ns) + 0.5f) / ns, t);
            ar += ((c >> 16) & 255) / 255.0f / (ns * ns); ag += ((c >> 8) & 255) / 255.0f / (ns * ns); ab += (c & 255) / 255.0f / (ns * ns);
        }
        used++;
    }
    if (!used) return;
    ar /= (float)used; ag /= (float)used; ab /= (float)used;
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
    CatalogPump();
    PumpOpen();
    if (g_reqIdx >= 0) { int ri = g_reqIdx; g_reqIdx = -1; StartLoad(ri, g_reqSpawn); }
    PumpLoad();
    if (g_mode == 1) CatalogStart();
    if (Pressed(VK_F10)) { g_glow = !g_glow; Status(g_glow ? "glow light on (F10 toggles)" : "glow light off (F10 toggles)"); }
    if (Pressed(VK_F9)) { g_invert = !g_invert; Status(g_invert ? "mouse inverted (F9 toggles)" : "mouse normal (F9 toggles)"); }
    CVehicle* v = FindPlayerVehicle(-1, false);
    bool cheat = CheatTyped();
    if (cheat && !g_focus && !g_naming) { ToggleMenu(); Log("PRS typed, menu=%d", g_menu ? 1 : 0); }
    if (g_menu) {
        UpdateMouse();
        HandleTyping();
    } else {
        if (Pressed(VK_NUMPAD0)) SetMode(0);
        if (g_mode == 1) {
            if (Pressed(VK_NUMPAD6)) QuickTex(1);
            if (Pressed(VK_NUMPAD4)) QuickTex(-1);
            if (Pressed(VK_NUMPAD9)) QuickTxd(1, 0);
            if (Pressed(VK_NUMPAD3)) QuickTxd(-1, 0);
        } else if (g_mode == 2) {
            if (Pressed(VK_NUMPAD6)) { g_design = DesignStep(g_design, 1); g_designCat = DesignCatOf(g_design); ApplySelToAll(); }
            if (Pressed(VK_NUMPAD4)) { g_design = DesignStep(g_design, -1); g_designCat = DesignCatOf(g_design); ApplySelToAll(); }
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
    UpdateDyns();
    AddGlowLights();
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
    DrawErrBanner();
    if (g_mode == 0) { CFont::DrawFonts(); return; }
    char buf[160];
    if (g_mode == 1) {
        RwTexture* t = CurTex();
        if (!t && g_loadedName[0]) sprintf(buf, "BodyTex | save '%s' | type PRS for menu", g_loadedName);
        else sprintf(buf, "BodyTex 1 | %s (%d/%d) | type PRS for menu", t ? t->name : "-", g_idx + 1, (int)g_tex.size());
    } else {
        sprintf(buf, "BodyTex 2 | %s | type PRS for menu", DESIGN_NAME[g_design]);
    }
    Text(20.0f, SH() * 0.85f, buf, C_GOLD_LT, 0.9f);
    if (g_status[0] && CTimer::m_snTimeInMilliseconds - g_statusT < 3000)
        Text(20.0f, SH() * 0.85f + SH() * 0.035f, g_status, C_GOLD, 0.8f);
    CFont::DrawFonts();
}

static void Shutdown() {
    g_abort = true;
    CancelLoad();
    if (g_scanThread) {
        WaitForSingleObject(g_scanThread, 1500);
        CloseHandle(g_scanThread);
        g_scanThread = nullptr;
    }
    CancelPending();
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
        Log("---- BodyTex v0.7 loaded ----");
        LogGameVer();
        Events::gameProcessEvent += Process;
        Events::drawHudEvent += DrawHud;
        Events::shutdownRwEvent += Shutdown;
    }
} bodyTexPlugin;

