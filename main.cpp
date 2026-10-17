// BodyTex.asi v1.2 - GTA San Andreas (1.0 US) - plugin-sdk
// NEW in v1.2: Animals, Brands and Food&Fun now have 32 animated designs each (at least 4 full pages in the menu).
//   Animals +19 (ids 322-340) | Brands +21 (ids 341-361) | Food&Fun +22 (ids 362-383). Old designs/ids untouched, old saves still load.
//   All 12 animated categories now have at least 4 full pages.
// NEW in v1.1: Party, Scenes and Soda now have 32 animated designs each (at least 4 full pages in the menu).
//   Party +22 (ids 261-282) | Scenes +18 (ids 283-300) | Soda +21 (ids 301-321). Old designs/ids untouched, old saves still load.
// NEW in v1.0: Space, Water and Gold now have 32 animated designs each (at least 4 full pages in the menu).
//   Space +28 (ids 175-202) | Water +29 (ids 203-231) | Gold +29 (ids 232-260). Old designs/ids untouched, old saves still load.
// NEW in v0.9: Matrix, Neon and Fire/Ice now have 32+ animated designs each (at least 4 full pages in the menu):
//   Matrix +22 (ids 104-125) | Neon +21 (ids 126-146) | Fire/Ice +28 (ids 147-174). Old designs/ids untouched.
// NEW in v0.8: 45 more animated designs in 4 NEW categories (old categories/ids untouched, old saves still load):
//   Soda (11) | Animals (13) | Brands (11, colours + patterns only, no logos) | Food & Fun (10)
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
static const int N_DESIGNS = 384;
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
    "Peacock feathers", "Dragon scales",                                                                       // 57-58
    // v0.8 Soda (59-69)
    "Soda: Cola", "Soda: Cherry cola", "Soda: Orange", "Soda: Lemon-lime", "Soda: Grape", "Soda: Root beer",
    "Soda: Blue raspberry", "Soda: Strawberry", "Soda: Energy drink", "Soda: Mojito mint", "Soda: Cream soda",
    // Animals (70-82)
    "Tiger stripes", "Leopard rosettes", "Cheetah run", "Zebra", "Cow spots", "Giraffe", "Snake skin",
    "Dalmatian", "Butterfly wings", "Fish scales", "Parrot feathers", "Wolf eyes in the forest", "Bee honeycomb",
    // Brands (83-93): colours + patterns only
    "Ferrari red & yellow", "Lamborghini hex", "Tiffany blue sparkle", "Gucci stripes", "Green coffee ripples",
    "Red & yellow fries", "Three white stripes", "Blue-garnet stripes", "Green sound waves", "Red curtain beams",
    "Purple glitch",
    // Food & Fun (94-103)
    "Candy swirl", "Sprinkles", "Watermelon", "Chocolate & caramel", "Pixel invaders", "Racing flag", "Camo",
    "Tie-dye", "Soap bubbles", "Confetti",
    // v0.9 Matrix (104-125)
    "Matrix: Gold rain", "Matrix: Cyan sentences", "Matrix: Purple binary", "Matrix: Orange text columns",
    "Matrix: White flicker", "Matrix: Pink rain", "Matrix: Rising green", "Matrix: Rising rainbow",
    "Matrix: Diagonal cyan", "Matrix: Diagonal rainbow", "Matrix: Hex green", "Matrix: Hex red",
    "Matrix: Radial rainbow", "Matrix: Radial blue", "Matrix: Gold binary streams", "Matrix: Cyan binary streams",
    "Matrix: Two-way green", "Matrix: Two-way neon", "Matrix: Fire code", "Matrix: Ice code",
    "Matrix: Sunset code", "Matrix: Toxic lime flicker",
    // v0.9 Neon (126-146)
    "Neon tunnel", "Neon triangles", "Neon hexagons", "Neon rain", "Neon spider web", "Neon zigzag",
    "Neon sine waves", "Neon diamonds", "Neon circles", "Neon DNA", "Neon scan lines", "Neon sparks",
    "Neon plus signs", "Neon vortex", "Neon checker", "Neon bars", "Neon road", "Neon ripples",
    "Neon heartbeat", "Neon fireworks", "Neon marquee",
    // v0.9 Fire/Ice (147-174)
    "Campfire", "Blue flame", "Toxic green flame", "Purple flame", "Inferno", "Rising embers", "Magma flow",
    "Flame tongues", "Fire rings", "Fire tornado", "Heat haze", "Glowing coals", "Phoenix feathers", "Volcano sparks",
    "Frost crystals", "Snowfall", "Blizzard", "Frozen lake cracks", "Icicles", "Glacier layers", "Snowflakes",
    "Dry ice fog", "Cold plasma", "Diamond ice", "Frozen waves", "Blue ice shimmer",
    "Fire & ice spiral", "Fire & ice yin-yang",
    // v1.0 Space (175-202)
    "Saturn rings", "Comet shower", "Supernova", "Pulsar beams", "Wormhole", "Meteor rain", "Planet horizon",
    "Cosmic dust", "Shooting stars", "Solar flare", "Constellations", "Orbiting planets", "Alien sky", "Asteroid field",
    "Warp speed", "Red giant", "Milky Way", "Neutron star", "Quasar jet", "Solar eclipse", "Cosmic web",
    "City lights from orbit", "Binary stars", "Cosmic waves", "UFO tractor beams", "Stardust spiral", "Big bang",
    "Rainbow nebula",
    // v1.0 Water (203-231)
    "Deep sea", "Underwater rays", "Rain on pond", "Whirlpool", "Rolling wave", "Rising bubbles", "Coral reef",
    "Shore foam", "Raindrops on glass", "Lagoon caustics", "Fountain", "River flow", "Sun glitter sea", "Moonlit sea",
    "Drop impact", "Kelp forest", "Ink in water", "Bioluminescence", "Foam lace", "Sand ripples", "Pool tiles",
    "Hot spring", "Stormy sea", "Seigaiha waves", "Lily pond", "Fish school", "Sonar pings", "Oil slick", "Rapids",
    // v1.0 Gold (232-260)
    "Liquid gold", "Gold foil", "Gold coins", "Gold dust", "Brushed gold", "Gold hexagons", "Art deco fans",
    "Gold glitter", "Gold bars", "Royal gold & purple", "Gold & red", "Gold leaf", "Gold chain", "Deco diamonds",
    "Gold rain", "Rose gold swirl", "Gold circuit", "Gold spiral", "Gold mandala", "Gold marble", "Molten gold",
    "Gold sun rays", "Gold scales", "Gold lightning", "Gold fireworks", "Gold & emerald", "Gold stripes",
    "Gold night stars", "Gold mirror",
    // v1.1 Party (261-282)
    "Disco ball", "Laser fan", "Glow sticks", "Rising balloons", "Firework bursts", "Stage spotlights", "Dance floor",
    "Streamers", "Sparklers", "Rainbow checker waves", "Strobe burst", "Beat rings", "Lava lamp", "Kaleidoscope",
    "Bubblegum swirl", "Glitter rain", "Marquee bulbs", "Pinata burst", "Rave tunnel", "Holo foil", "Vinyl record",
    "Floor spots",
    // v1.1 Scenes (283-300)
    "Lighthouse storm", "Desert dunes & moon", "Cherry blossom", "Erupting volcano", "Pirate ship", "Rocket launch",
    "Moonlit castle", "Sunflower field", "Windmill sunset", "City skyline night", "Rainy neon window",
    "Dew spider web", "Wolf howling", "Hot air balloons", "Firefly forest", "Aurora lake", "Tornado", "Snowy village",
    // v1.1 Soda (301-321)
    "Soda: Peach", "Soda: Pineapple", "Soda: Watermelon", "Soda: Coconut lime", "Soda: Ginger ale",
    "Soda: Tonic water", "Soda: Lemonade", "Soda: Pink grapefruit", "Soda: Blueberry", "Soda: Green apple",
    "Soda: Mango", "Soda: Black currant", "Soda: Rainbow layers", "Soda: Pouring", "Soda: Ice cubes in cola",
    "Soda: Fizz close-up", "Soda: Straw swirl", "Soda: Cold can", "Soda: Float", "Soda: Slushie swirl",
    "Soda: Fizzy geyser",
    // v1.2 Animals (322-340)
    "Black panther", "Snow leopard", "White tiger", "Jaguar rosettes", "Lion mane", "Flamingo feathers",
    "Chameleon skin", "Poison dart frog", "Clownfish", "Betta fins", "Octopus skin", "Crocodile skin",
    "Owl feathers", "Ladybugs", "Dragonfly wing", "Bat swarm", "Sea turtle shell", "Fox fur", "Hummingbird shimmer",
    // v1.2 Brands (341-361): colours + patterns only
    "Martini stripes", "Gulf racing livery", "Black & gold pinstripe", "Fluted green dial", "Brown monogram lattice",
    "Beige tartan", "Blue & silver energy", "Pink & orange donuts", "Hazard stripes", "Racing tricolour",
    "Silver arrow brushed", "Blue & black split", "Papaya speed lines", "Red white & blue swirl", "Sunset social gradient",
    "Toy bricks", "Pixel blocks", "Orange & black flames", "Red & white slashes", "Hot pink glitter", "Electric red charge",
    // v1.2 Food & Fun (362-383)
    "Pepperoni pizza", "Donut glaze", "Ice cream swirl", "Burger layers", "Sushi rolls", "Popcorn", "Swiss cheese",
    "Strawberry skin", "Orange slice", "Kiwi slice", "Chomper dots", "Falling blocks", "Cube stickers", "Tumbling dice",
    "Poker chips", "Bubble tea", "Smiley faces", "Floating notes", "Pop-art dots", "Rainbow flag wave", "Jelly beans",
    "Cotton candy"
};
enum { DC_MATRIX = 0, DC_NEON, DC_FIRE, DC_SPACE, DC_WATER, DC_GOLD, DC_PARTY, DC_SCENE, DC_SODA, DC_ANIMAL, DC_BRAND, DC_FUN, N_DC };
static const unsigned short DCL_MATRIX[] = {3, 36, 37, 38, 39, 40, 41, 42, 43, 44,
    104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125};
static const unsigned short DCL_NEON[]   = {5, 6, 7, 8, 10, 12, 23, 28, 29, 32, 22,
    126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146};
static const unsigned short DCL_FIRE[]   = {1, 14, 15, 30,
    147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174};
static const unsigned short DCL_SPACE[]  = {13, 26, 18, 9,
    175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202};
static const unsigned short DCL_WATER[]  = {21, 33, 24,
    203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231};
static const unsigned short DCL_GOLD[]   = {11, 27, 35,
    232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260};
static const unsigned short DCL_PARTY[]  = {0, 2, 4, 16, 17, 19, 20, 25, 31, 34,
    261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282};
static const unsigned short DCL_SCENE[]  = {45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58,
    283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300};
static const unsigned short DCL_SODA[]   = {59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
    301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321};
static const unsigned short DCL_ANIMAL[] = {70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82,
    322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340};
static const unsigned short DCL_BRAND[]  = {83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
    341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361};
static const unsigned short DCL_FUN[]    = {94, 95, 96, 97, 98, 99, 100, 101, 102, 103,
    362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383};
struct DesignCat { const char* name; const unsigned short* ids; int n; };
static const DesignCat DCATS[N_DC] = {
    {"Matrix",  DCL_MATRIX, (int)(sizeof(DCL_MATRIX) / sizeof(unsigned short))},
    {"Neon",    DCL_NEON,   (int)(sizeof(DCL_NEON) / sizeof(unsigned short))},
    {"Fire/Ice",DCL_FIRE,   (int)(sizeof(DCL_FIRE) / sizeof(unsigned short))},
    {"Space",   DCL_SPACE,  (int)(sizeof(DCL_SPACE) / sizeof(unsigned short))},
    {"Water",   DCL_WATER,  (int)(sizeof(DCL_WATER) / sizeof(unsigned short))},
    {"Gold",    DCL_GOLD,   (int)(sizeof(DCL_GOLD) / sizeof(unsigned short))},
    {"Party",   DCL_PARTY,  (int)(sizeof(DCL_PARTY) / sizeof(unsigned short))},
    {"Scenes",  DCL_SCENE,  (int)(sizeof(DCL_SCENE) / sizeof(unsigned short))},
    {"Soda",    DCL_SODA,   (int)(sizeof(DCL_SODA) / sizeof(unsigned short))},
    {"Animals", DCL_ANIMAL, (int)(sizeof(DCL_ANIMAL) / sizeof(unsigned short))},
    {"Brands",  DCL_BRAND,  (int)(sizeof(DCL_BRAND) / sizeof(unsigned short))},
    {"Food&Fun",DCL_FUN,    (int)(sizeof(DCL_FUN) / sizeof(unsigned short))}
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
static bool DesignIsScene(int d) { return d >= 45 && d < 59; }


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


// ---------------- v0.8: 45 more animated designs (ids 59..103) ----------------
// Soda (59-69) | Animals (70-82) | Brands (83-93, colours + patterns only, no logos) | Food & Fun (94-103)
struct NRgb { float r, g, b; };
static inline NRgb nMix(NRgb a, NRgb b, float t) { return { bMix(a.r, b.r, t), bMix(a.g, b.g, t), bMix(a.b, b.b, t) }; }
static inline void nSet(float& r, float& g, float& b, NRgb c) { r = c.r; g = c.g; b = c.b; }
static inline float nMod(float x, float m) { return x - m * floorf(x / m); }
static const float kTau = 6.2831853f;

// ---- Soda: liquid gradient + rising bubbles + foam ----
struct SodaDef { NRgb top, bot, bub; float fizz, foam; };
static const SodaDef SODAS[11] = {
    {{0.30f, 0.10f, 0.04f}, {0.05f, 0.01f, 0.01f}, {0.95f, 0.85f, 0.75f}, 1.0f, 0.9f},   // 59 Cola
    {{0.60f, 0.03f, 0.08f}, {0.15f, 0.00f, 0.03f}, {1.00f, 0.75f, 0.80f}, 1.0f, 0.7f},   // 60 Cherry cola
    {{1.00f, 0.58f, 0.05f}, {0.90f, 0.25f, 0.00f}, {1.00f, 0.92f, 0.65f}, 1.2f, 0.6f},   // 61 Orange soda
    {{0.85f, 1.00f, 0.25f}, {0.30f, 0.80f, 0.10f}, {1.00f, 1.00f, 0.85f}, 1.3f, 0.5f},   // 62 Lemon-lime
    {{0.65f, 0.25f, 0.95f}, {0.20f, 0.03f, 0.40f}, {0.92f, 0.80f, 1.00f}, 1.0f, 0.6f},   // 63 Grape soda
    {{0.40f, 0.20f, 0.06f}, {0.10f, 0.04f, 0.01f}, {1.00f, 0.92f, 0.78f}, 0.8f, 1.6f},   // 64 Root beer (thick foam)
    {{0.10f, 0.75f, 1.00f}, {0.00f, 0.15f, 0.80f}, {0.80f, 1.00f, 1.00f}, 1.2f, 0.5f},   // 65 Blue raspberry
    {{1.00f, 0.40f, 0.55f}, {0.80f, 0.05f, 0.22f}, {1.00f, 0.88f, 0.92f}, 1.1f, 0.6f},   // 66 Strawberry soda
    {{0.75f, 0.85f, 0.98f}, {0.04f, 0.14f, 0.55f}, {1.00f, 1.00f, 1.00f}, 2.2f, 0.3f},   // 67 Energy drink
    {{0.55f, 1.00f, 0.72f}, {0.04f, 0.50f, 0.30f}, {0.95f, 1.00f, 0.95f}, 1.4f, 0.5f},   // 68 Mojito mint
    {{1.00f, 0.88f, 0.45f}, {0.72f, 0.45f, 0.10f}, {1.00f, 0.97f, 0.85f}, 0.9f, 0.8f}    // 69 Cream soda
};
static void NSodaD(const SodaDef& d, float u, float v, float t, float& r, float& g, float& b) {
    float w = 0.035f * sinf(u * 9.0f + t * 1.5f) + 0.025f * sinf(u * 17.0f - t * 2.2f);
    NRgb c = nMix(d.top, d.bot, Cl(v + w));
    float sh = 0.07f * sinf((u + v) * 12.0f - t * 2.0f);
    float shaft = bSm(0.12f, 0.0f, fabsf(u - 0.22f - 0.05f * sinf(t * 0.7f) - v * 0.15f)) * 0.16f;
    c.r += sh + shaft; c.g += sh + shaft; c.b += sh + shaft;
    const float COLS = 16.0f;
    int cx = (int)floorf(u * COLS);
    float acc = 0.0f, rim = 0.0f;
    for (int dx = -1; dx <= 1; dx++) {
        int ci = cx + dx;
        for (int j = 0; j < 2; j++) {
            float h = Hh(ci, j, 3);
            float sp = (0.12f + 0.30f * Hh(ci, j, 5)) * d.fizz;
            float by = 1.1f - Fr(t * sp + h) * 1.25f;
            float bx = (ci + 0.2f + 0.6f * Hh(ci, j, 7) + 0.18f * sinf(t * 2.0f + h * 20.0f)) / COLS;
            float rad = (0.010f + 0.020f * Hh(ci, j, 9)) * (0.7f + 0.6f * (1.0f - by));
            float dd = bLen(u - bx, v - by);
            acc += bSm(rad, rad * 0.55f, dd) * 0.55f;
            rim += bSm(rad * 0.25f, 0.0f, fabsf(dd - rad * 0.8f)) * 0.5f;
        }
    }
    c = nMix(c, d.bub, Cl(acc * 0.6f + rim * 0.5f));
    float fm = bSm(0.09f * d.foam + 0.015f * sinf(u * 25.0f + t * 2.0f), 0.0f, v) * Cl(d.foam);
    c = nMix(c, d.bub, fm * 0.85f);
    nSet(r, g, b, c);
}
static void NSoda(int k, float u, float v, float t, float& r, float& g, float& b) { NSodaD(SODAS[k], u, v, t, r, g, b); }

// ---- helpers for the animal / brand patterns ----
// jittered voronoi: nearest (f1) and second nearest (f2) cell distance + a hash of the nearest cell
static void nVor(float x, float y, float t, float anim, float& f1, float& f2, float& hid) {
    int ix = (int)floorf(x), iy = (int)floorf(y);
    float fx = x - ix, fy = y - iy;
    f1 = f2 = 9.0f; hid = 0.0f;
    for (int j = -1; j <= 1; j++) for (int i = -1; i <= 1; i++) {
        float h1 = Hh(ix + i, iy + j, 21), h2 = Hh(ix + i, iy + j, 22);
        float px = i + 0.5f + (h1 - 0.5f) * 0.6f + 0.12f * sinf(t * anim + h1 * 20.0f);
        float py = j + 0.5f + (h2 - 0.5f) * 0.6f + 0.12f * cosf(t * anim + h2 * 20.0f);
        float d = bLen(px - fx, py - fy);
        if (d < f1) { f2 = f1; f1 = d; hid = Hh(ix + i, iy + j, 23); }
        else if (d < f2) f2 = d;
    }
}
// one spot per grid cell: fill = whole disc, inner = smaller disc (for rosettes)
static void nSpots(float u, float v, float scale, float t, float scroll, float minH, float rMin, float rMax,
                   float& fill, float& inner, float& hid) {
    float x = u * scale + t * scroll, y = v * scale;
    int ix = (int)floorf(x), iy = (int)floorf(y);
    float fx = x - ix, fy = y - iy;
    float h = Hh(ix, iy, 31);
    float cx = 0.5f + (Hh(ix, iy, 32) - 0.5f) * 0.3f, cy = 0.5f + (Hh(ix, iy, 33) - 0.5f) * 0.3f;
    float rad = (rMin + (rMax - rMin) * Hh(ix, iy, 34)) * (0.92f + 0.08f * sinf(t * 1.5f + h * 30.0f));
    float d = bLen(fx - cx, fy - cy);
    hid = h;
    if (h <= minH) { fill = inner = 0.0f; return; }
    fill = bSm(rad, rad - 0.04f, d);
    inner = bSm(rad * 0.62f, rad * 0.62f - 0.04f, d);
}
// hexagonal grid: returns distance to the cell border (0 at the edge, 0.5 in the middle) and a cell hash
static float nHex(float x, float y, float& hid) {
    const float rx = 1.0f, ry = 1.7320508f;
    float ax = nMod(x, rx) - rx * 0.5f, ay = nMod(y, ry) - ry * 0.5f;
    float bx = nMod(x - rx * 0.5f, rx) - rx * 0.5f, by = nMod(y - ry * 0.5f, ry) - ry * 0.5f;
    float gx, gy;
    if (ax * ax + ay * ay < bx * bx + by * by) { gx = ax; gy = ay; hid = Hh((int)floorf(x / rx), (int)floorf(y / ry), 41); }
    else { gx = bx; gy = by; hid = Hh((int)floorf((x - 0.5f * rx) / rx) + 100, (int)floorf((y - 0.5f * ry) / ry) + 100, 41); }
    gx = fabsf(gx); gy = fabsf(gy);
    return 0.5f - bMax(gx, gx * 0.5f + gy * 0.8660254f);
}
static inline float nBar(float q, float lo, float hi) { return bSm(lo, lo + 0.04f, q) * bSm(hi, hi - 0.04f, q); }

// ---- Animals ----
static void NTiger(float u, float v, float t, float& r, float& g, float& b) {
    float n = bFbm(u * 3.0f + t * 0.05f, v * 3.0f);
    float w = u * 8.0f + n * 3.2f + 0.5f * sinf(v * 3.0f + t * 0.6f) + t * 0.12f;
    float stripe = bSm(0.16f, 0.06f, fabsf(Fr(w) - 0.5f));
    float fur = 0.86f + 0.14f * Hh((int)(u * 180), (int)(v * 180), 3);
    r = bMix(1.00f * fur, 0.04f, stripe); g = bMix(0.52f * fur, 0.02f, stripe); b = bMix(0.08f * fur, 0.0f, stripe);
}
static void NLeopard(float u, float v, float t, float& r, float& g, float& b) {
    float fill, inner, h; nSpots(u, v, 6.0f, t, 0.08f, 0.15f, 0.22f, 0.32f, fill, inner, h);
    float fur = 0.9f + 0.1f * Hh((int)(u * 170), (int)(v * 170), 4);
    float ring = Cl(fill - inner);
    r = 0.92f * fur; g = 0.68f * fur; b = 0.25f * fur;
    r = bMix(r, 0.75f * fur, inner); g = bMix(g, 0.50f * fur, inner); b = bMix(b, 0.15f * fur, inner);
    r = bMix(r, 0.12f, ring); g = bMix(g, 0.06f, ring); b = bMix(b, 0.02f, ring);
}
static void NCheetah(float u, float v, float t, float& r, float& g, float& b) {
    float fill, inner, h; nSpots(u, v, 14.0f, t, 0.35f, 0.25f, 0.14f, 0.26f, fill, inner, h);
    float fur = 0.9f + 0.1f * Hh((int)(u * 170), (int)(v * 170), 5);
    r = bMix(0.95f * fur, 0.05f, fill); g = bMix(0.75f * fur, 0.03f, fill); b = bMix(0.30f * fur, 0.01f, fill);
}
static void NZebra(float u, float v, float t, float& r, float& g, float& b) {
    float n = bFbm(u * 3.0f, v * 3.0f + t * 0.03f);
    float s = sinf((u * 0.8f + v * 0.6f) * 22.0f + n * 9.0f - t * 0.8f);
    float m = bSm(-0.1f, 0.1f, s);
    float c = 0.03f + 0.93f * m;
    r = c; g = c; b = c * 0.97f + 0.02f;
}
static void NCow(float u, float v, float t, float& r, float& g, float& b) {
    float n = bFbm(u * 2.5f + t * 0.03f, v * 2.5f) + 0.03f * sinf(t * 0.5f);
    float m = bSm(0.52f, 0.56f, n);
    float c = bMix(0.95f, 0.05f, m);
    r = c; g = c; b = c * 0.97f;
    float pink = bSm(0.62f, 0.7f, bFbm(u * 4.0f + 7.0f, v * 4.0f)) * (1.0f - m);
    r = bMix(r, 1.0f, pink * 0.5f); g = bMix(g, 0.75f, pink * 0.5f); b = bMix(b, 0.75f, pink * 0.5f);
}
static void NGiraffe(float u, float v, float t, float& r, float& g, float& b) {
    float f1, f2, h; nVor(u * 5.0f, v * 5.0f, t, 0.4f, f1, f2, h);
    float edge = bSm(0.07f, 0.14f, f2 - f1);
    float shade = 0.75f + 0.5f * h;
    r = bMix(0.95f, 0.85f * shade, edge); g = bMix(0.88f, 0.52f * shade, edge); b = bMix(0.70f, 0.14f * shade, edge);
}
static void NSnake(float u, float v, float t, float& r, float& g, float& b) {
    float a = (u + v) * 8.0f + t * 0.3f, bb = (u - v) * 8.0f;
    float fa = Fr(a) - 0.5f, fb = Fr(bb) - 0.5f;
    float d = bMax(fabsf(fa), fabsf(fb));
    float h = Hh((int)floorf(a), (int)floorf(bb), 2);
    float cr = 0.10f + 0.20f * h, cg = 0.50f + 0.30f * h, cb = 0.10f;
    if (h > 0.72f) { cr = 0.25f; cg = 0.14f; cb = 0.05f; }
    float sheen = 0.5f + 0.5f * sinf(u * 6.0f - t * 1.5f);
    float k = (0.65f + 0.45f * sheen * (1.0f - d)) * bMix(1.0f, 0.25f, bSm(0.38f, 0.5f, d));
    r = cr * k; g = cg * k; b = cb * k;
}
static void NDalmatian(float u, float v, float t, float& r, float& g, float& b) {
    float fill, inner, h; nSpots(u, v, 5.0f, t, 0.05f, 0.3f, 0.14f, 0.30f, fill, inner, h);
    float c = bMix(0.96f, 0.03f, fill);
    r = c; g = c; b = c;
}
static void NButterfly(float u, float v, float t, float& r, float& g, float& b) {
    float f = 0.55f + 0.45f * fabsf(cosf(t * 2.5f));
    float X = fabsf(u - 0.5f) * 2.0f / f, Y = v;
    float dU = bEll(X, Y, 0.55f, 0.32f, 0.50f, 0.30f);
    float dL = bEll(X, Y, 0.42f, 0.70f, 0.34f, 0.24f);
    float d = bMin(dU, dL);
    float inside = bSm(0.01f, -0.01f, d);
    float ang = atan2f(Y - 0.5f, X);
    float vein = bSm(0.10f, 0.05f, fabsf(sinf(ang * 9.0f)));
    float border = bSm(-0.06f, -0.02f, d);
    float dots = bSm(0.016f, 0.008f, fabsf(Fr(ang * 5.0f) - 0.5f) * 0.1f + fabsf(d + 0.07f));
    float cr = 1.0f, cg = 0.50f + 0.15f * sinf(t * 2.0f + X * 6.0f), cb = 0.02f;
    cr = bMix(cr, 0.05f, vein * 0.8f); cg = bMix(cg, 0.02f, vein * 0.8f); cb = bMix(cb, 0.0f, vein * 0.8f);
    cr = bMix(cr, 0.04f, border); cg = bMix(cg, 0.02f, border); cb = bMix(cb, 0.02f, border);
    cr = bMix(cr, 1.0f, dots); cg = bMix(cg, 1.0f, dots); cb = bMix(cb, 1.0f, dots);
    float bgn = bFbm(u * 3.0f + t * 0.1f, v * 3.0f);
    r = bMix(0.02f + 0.05f * bgn, cr, inside); g = bMix(0.10f + 0.12f * bgn, cg, inside); b = bMix(0.18f + 0.2f * bgn, cb, inside);
    float body = bSm(0.022f, 0.012f, fabsf(u - 0.5f)) * bSm(0.15f, 0.2f, v) * bSm(0.88f, 0.82f, v);
    r = bMix(r, 0.02f, body); g = bMix(g, 0.02f, body); b = bMix(b, 0.02f, body);
}
static void NFishScales(float u, float v, float t, float& r, float& g, float& b) {
    const float N = 10.0f;
    float sy = v * N, row = floorf(sy);
    float sx = u * N + (((int)row) & 1 ? 0.5f : 0.0f);
    float fx = Fr(sx) - 0.5f, fy = Fr(sy);
    float d = bLen(fx, fy - 0.12f);
    float inS = bSm(0.62f, 0.5f, d);
    float hs = Hh((int)floorf(sx), (int)row, 8);
    Hsv(0.5f + 0.10f * hs + 0.06f * sinf(t * 0.8f + u * 4.0f), 0.55f, 0.95f, r, g, b);
    float rim = bSm(0.44f, 0.56f, d);
    float wave = expf(-powf(Fr(u * 0.7f + v * 0.4f - t * 0.3f) - 0.5f, 2.0f) * 60.0f);
    float k = (0.55f + 0.45f * (1.0f - d)) * (1.0f - 0.5f * rim) * (0.3f + 0.7f * inS);
    r = r * k + wave * 0.5f * inS; g = g * k + wave * 0.5f * inS; b = b * k + wave * 0.5f * inS;
}
static void NParrot(float u, float v, float t, float& r, float& g, float& b) {
    float x = Fr(v * 1.1f + 0.15f * sinf(u * 6.0f + t * 1.3f) + t * 0.05f);
    float hue = (x < 0.5f) ? x * 0.35f : 0.175f + (x - 0.5f) * 0.9f;       // red -> yellow -> green -> blue
    Hsv(hue, 0.95f, 1.0f, r, g, b);
    float barb = 0.82f + 0.18f * sinf(u * 120.0f + v * 40.0f + sinf(v * 9.0f) * 3.0f);
    r *= barb; g *= barb; b *= barb;
}
static void NWolfEyes(float u, float v, float t, float& r, float& g, float& b) {
    float n = bFbm(u * 3.0f + t * 0.05f, v * 3.0f - t * 0.03f);
    float tree = bSm(0.05f, 0.03f, fabsf(Fr(u * 6.0f + 0.4f * bVn(v * 2.0f, 1.0f)) - 0.5f));
    r = 0.02f + 0.05f * n; g = 0.04f + 0.09f * n; b = 0.07f + 0.13f * n;
    float md = bLen(u - 0.8f, v - 0.15f);
    float mg = expf(-md * md * 14.0f);
    r += 0.22f * mg; g += 0.26f * mg; b += 0.36f * mg;
    r *= 1.0f - 0.8f * tree; g *= 1.0f - 0.8f * tree; b *= 1.0f - 0.8f * tree;
    static const float E[4][3] = {{0.25f, 0.55f, 1.0f}, {0.65f, 0.72f, 0.8f}, {0.50f, 0.35f, 0.6f}, {0.82f, 0.62f, 0.5f}};
    for (int k = 0; k < 4; k++) {
        float ph = Fr(t * 0.18f + k * 0.31f);
        float open = 1.0f - bSm(0.92f, 0.94f, ph) * (1.0f - bSm(0.97f, 0.99f, ph));
        float rad = 0.022f * E[k][2];
        for (int s = -1; s <= 1; s += 2) {
            float cx = E[k][0] + s * 0.06f * E[k][2], cy = E[k][1];
            float d = bLen(u - cx, (v - cy) * 1.8f);
            float core = bSm(rad, rad * 0.6f, d) * open;
            float halo = expf(-(d * d) / (rad * rad * 9.0f)) * 0.4f * open;
            float slit = bSm(rad * 0.25f, rad * 0.12f, fabsf(u - cx)) * core;
            r += core * 1.0f + halo * 0.9f; g += core * 0.85f + halo * 0.7f; b += core * 0.1f + halo * 0.1f;
            r -= slit * 1.0f; g -= slit * 0.85f; b -= slit * 0.1f;
        }
    }
}
static void NHoneycomb(float u, float v, float t, float& r, float& g, float& b) {
    float h; float e = nHex(u * 6.0f, v * 6.0f, h);
    float cell = bSm(0.03f, 0.07f, e);
    float glow = 0.5f + 0.5f * sinf(u * 7.0f + v * 5.0f - t * 2.0f + h * 6.0f);
    float k = 0.55f + 0.45f * glow;
    r = bMix(0.25f, (1.0f * k), cell); g = bMix(0.12f, (0.68f * k) * (0.85f + 0.15f * h), cell); b = bMix(0.02f, 0.05f * k, cell);
    float hl = bSm(0.30f, 0.44f, e) * 0.25f * glow;
    r += hl; g += hl * 0.8f;
}

// ---- Brands: colour schemes + patterns inspired by the brand, no logos or text ----
static void NFerrari(float u, float v, float t, float& r, float& g, float& b) {
    float shade = 0.72f + 0.28f * (1.0f - v);
    r = 0.92f * shade; g = 0.03f * shade; b = 0.03f * shade;
    float yd = fabsf(v - 0.5f - 0.07f * sinf(u * 6.0f - t * 2.0f));
    float y = bSm(0.060f, 0.045f, yd);
    r = bMix(r, 1.0f, y); g = bMix(g, 0.85f, y); b = bMix(b, 0.0f, y);
    float gl = expf(-powf((Fr(u * 0.7f + v * 0.4f - t * 0.22f) - 0.5f) * 6.0f, 2.0f)) * 0.35f;
    r += gl; g += gl; b += gl;
}
static void NLambo(float u, float v, float t, float& r, float& g, float& b) {
    float h; float e = nHex(u * 7.0f, v * 7.0f, h);
    float edge = bSm(0.06f, 0.0f, e);
    float wave = 0.5f + 0.5f * sinf(u * 8.0f + v * 5.0f - t * 3.0f);
    r = 0.03f + 0.05f * h; g = 0.03f + 0.05f * h; b = 0.03f + 0.04f * h;
    float fillY = (h > 0.7f) ? wave * 0.25f : 0.0f;
    r += fillY * 1.0f; g += fillY * 0.8f;
    float k = 0.35f + 0.65f * wave;
    r += edge * 1.0f * k; g += edge * 0.80f * k; b += edge * 0.0f;
}
static void NTiffany(float u, float v, float t, float& r, float& g, float& b) {
    float w = 0.5f + 0.5f * sinf(u * 5.0f + v * 3.0f - t * 0.8f);
    r = 0.50f * (0.9f + 0.1f * w); g = 0.84f * (0.9f + 0.1f * w); b = 0.81f * (0.9f + 0.1f * w);
    float yd = fabsf(v - 0.5f - 0.05f * sinf(u * 5.0f - t));
    float rb = bSm(0.035f, 0.025f, bMin(fabsf(yd - 0.09f), fabsf(yd + 0.0f)));
    r = bMix(r, 1.0f, rb); g = bMix(g, 1.0f, rb); b = bMix(b, 1.0f, rb);
    const float N = 10.0f;
    int ci = (int)floorf(u * N), cj = (int)floorf(v * N);
    float h = Hh(ci, cj, 6);
    if (h > 0.9f) {
        float fx = Fr(u * N) - 0.5f, fy = Fr(v * N) - 0.5f;
        float tw = powf(0.5f + 0.5f * sinf(t * 3.0f + h * 40.0f), 3.0f);
        float st = expf(-fabsf(fx) * 14.0f - fabsf(fy) * 2.0f) + expf(-fabsf(fy) * 14.0f - fabsf(fx) * 2.0f);
        float s = bMin(1.0f, st * tw);
        r += s; g += s; b += s;
    }
}
static void NGucci(float u, float v, float t, float& r, float& g, float& b) {
    float x = Fr(u * 2.0f + t * 0.12f + 0.04f * sinf(v * 10.0f + t));
    float rm = bSm(0.36f, 0.38f, x) * bSm(0.64f, 0.62f, x);
    r = bMix(0.0f, 0.78f, rm); g = bMix(0.33f, 0.05f, rm); b = bMix(0.20f, 0.08f, rm);
    float gl = 0.5f + 0.5f * sinf((u + v) * 18.0f - t * 3.0f);
    float sp = (Hh((int)(u * 60), (int)(v * 60), (int)(t * 4)) > 0.985f) ? 1.0f : 0.0f;
    r += gl * 0.05f + sp * 0.9f; g += gl * 0.05f + sp * 0.75f; b += sp * 0.2f;
}
static void NGreenCafe(float u, float v, float t, float& r, float& g, float& b) {
    float rr = bLen(u - 0.5f, v - 0.5f);
    float rip = bSm(0.72f, 1.0f, sinf(rr * 34.0f - t * 3.0f));
    float n = bFbm(u * 3.0f + t * 0.1f, v * 3.0f);
    r = 0.0f + 0.05f * n; g = 0.38f + 0.1f * n; b = 0.24f + 0.06f * n;
    r = bMix(r, 0.95f, rip * 0.45f); g = bMix(g, 0.95f, rip * 0.45f); b = bMix(b, 0.9f, rip * 0.45f);
}
static void NFries(float u, float v, float t, float& r, float& g, float& b) {
    float x = u * 8.0f; int ci = (int)floorf(x); float fx = Fr(x) - 0.5f;
    float hgt = 0.35f + 0.35f * (0.5f + 0.5f * sinf(t * 2.0f + ci * 1.3f));
    float top = 1.0f - hgt;
    float m = bSm(0.38f, 0.34f, fabsf(fx)) * bSm(top, top + 0.015f, v);
    float rr = bLen(u - 0.5f, v - 0.5f);
    float br = 0.85f - 0.3f * rr;
    r = br; g = 0.05f * br; b = 0.03f * br;
    float sh = 0.8f + 0.2f * (1.0f - fabsf(fx) * 2.0f);
    r = bMix(r, 1.0f * sh, m); g = bMix(g, 0.78f * sh, m); b = bMix(b, 0.0f, m);
}
static void NThreeStripes(float u, float v, float t, float& r, float& g, float& b) {
    float q = Fr((u - 0.55f * v) * 1.2f + t * 0.12f) * 7.0f;
    float m = nBar(q, 0.0f, 1.0f) + nBar(q, 2.0f, 3.0f) + nBar(q, 4.0f, 5.0f);
    m = Cl(m);
    float c = bMix(0.03f, 0.96f, m);
    r = c; g = c; b = c;
}
static void NBarca(float u, float v, float t, float& r, float& g, float& b) {
    float x = u * 6.0f + 0.25f * sinf(v * 5.0f - t * 2.0f);
    int i = (int)floorf(x); float f = Fr(x);
    float cr, cg, cb;
    if (i & 1) { cr = 0.0f; cg = 0.30f; cb = 0.60f; } else { cr = 0.65f; cg = 0.10f; cb = 0.25f; }
    float sheen = 0.88f + 0.12f * sinf(v * 5.0f - t * 2.0f + u * 3.0f);
    float gold = bSm(0.04f, 0.0f, fminf(f, 1.0f - f));
    r = bMix(cr * sheen, 0.95f, gold); g = bMix(cg * sheen, 0.75f, gold); b = bMix(cb * sheen, 0.1f, gold);
}
static void NGreenWaves(float u, float v, float t, float& r, float& g, float& b) {
    float d = bLen(u - 0.1f, v - 1.15f);
    float w = Fr(d * 4.0f - t * 0.6f);
    float a = bSm(0.0f, 0.06f, w) * bSm(0.55f, 0.45f, w);
    float fade = Cl(1.2f - d);
    r = 0.07f; g = 0.07f; b = 0.07f;
    r = bMix(r, 0.12f, a * fade); g = bMix(g, 0.84f, a * fade); b = bMix(b, 0.38f, a * fade);
}
static void NRedCurtain(float u, float v, float t, float& r, float& g, float& b) {
    float x = u * 9.0f; int ci = (int)floorf(x); float fx = Fr(x);
    float h = Hh(ci, 0, 51);
    float beam = 0.35f + 0.65f * (0.5f + 0.5f * sinf(t * 1.2f + h * 20.0f + v * 3.0f * (h > 0.5f ? 1.0f : -1.0f)));
    float core = bSm(0.5f, 0.1f, fabsf(fx - 0.5f));
    r = 0.03f + 0.9f * beam * core; g = 0.0f + 0.04f * beam * core; b = 0.01f + 0.07f * beam * core;
    float fade = 0.55f + 0.45f * v;
    r *= fade; g *= fade; b *= fade;
}
static void NPurpleGlitch(float u, float v, float t, float& r, float& g, float& b) {
    int row = (int)floorf(v * 24.0f), ts = (int)floorf(t * 6.0f);
    float gl = Hh(row, ts, 61);
    float off = gl > 0.88f ? (Hh(row, ts, 62) - 0.5f) * 0.3f : 0.0f;
    float uu = u + off;
    float base = 0.18f + 0.39f * (1.0f - v);
    r = base; g = 0.06f + 0.21f * (1.0f - v); b = 0.35f + 0.65f * (1.0f - v);
    float hb = Hh((int)floorf(uu * 12.0f), (int)floorf(v * 12.0f), (int)floorf(t * 2.0f));
    if (hb > 0.72f) { r += 0.25f; g += 0.12f; b += 0.2f; }
    if (hb > 0.975f || (gl > 0.88f && Hh(row, ts, 63) > 0.8f)) { r = g = b = 1.0f; }
}

// ---- Food & Fun ----
static void NCandySwirl(float u, float v, float t, float& r, float& g, float& b) {
    float x = u - 0.5f, y = v - 0.5f, rr = bLen(x, y), ang = atan2f(y, x);
    float s = Fr(ang / kTau * 6.0f + rr * 4.0f - t * 0.35f);
    float m = bSm(0.0f, 0.03f, s) * bSm(0.5f, 0.47f, s);
    float shade = 0.88f + 0.12f * sinf(rr * 20.0f - t * 2.0f);
    r = bMix(1.0f, 0.95f, m) * shade; g = bMix(0.97f, 0.08f, m) * shade; b = bMix(0.97f, 0.18f, m) * shade;
}
// falling little pieces in a jittered grid: kind 0 = sprinkles (capsules), 1 = confetti (flipping rectangles)
static void NPieces(float u, float v, float t, float scale, float fall, int kind, NRgb bg, float& r, float& g, float& b) {
    float x = u * scale, y = v * scale - t * fall;
    int ix = (int)floorf(x), iy = (int)floorf(y);
    float fx = x - ix, fy = y - iy;
    nSet(r, g, b, bg);
    for (int j = -1; j <= 1; j++) for (int i = -1; i <= 1; i++) {
        int ci = ix + i, cj = iy + j;
        float h1 = Hh(ci, cj, 71), h2 = Hh(ci, cj, 72), h3 = Hh(ci, cj, 73), h4 = Hh(ci, cj, 74);
        if (h4 < 0.25f) continue;
        float px = fx - (i + 0.5f + (h1 - 0.5f) * 0.5f), py = fy - (j + 0.5f + (h2 - 0.5f) * 0.5f);
        float ang = h3 * kTau + t * (h1 - 0.5f) * (kind ? 3.0f : 0.6f);
        float ca = cosf(ang), sa = sinf(ang);
        float qx = px * ca + py * sa, qy = -px * sa + py * ca;
        float cov;
        if (kind == 0) cov = bSm(0.01f, -0.01f, bCap(qx, qy, -0.17f, 0.0f, 0.17f, 0.0f, 0.07f));
        else {
            float flip = fabsf(cosf(t * 3.0f * (0.5f + h2) + h1 * 10.0f)) + 0.08f;
            cov = bSm(0.17f, 0.15f, fabsf(qx)) * bSm(0.11f * flip + 0.01f, 0.11f * flip - 0.01f, fabsf(qy));
        }
        if (cov > 0.05f) {
            float cr, cg, cb; Hsv(Hh(ci, cj, 75), 0.85f, 1.0f, cr, cg, cb);
            r = bMix(r, cr, cov); g = bMix(g, cg, cov); b = bMix(b, cb, cov);
        }
    }
}
static void NWatermelon(float u, float v, float t, float& r, float& g, float& b) {
    r = 0.95f; g = 0.12f + 0.2f * v * 0.5f; b = 0.22f + 0.1f * v * 0.5f;
    float rm = fminf(v, 1.0f - v) - 0.02f * sinf(u * 6.0f + t);
    float x = u * 7.0f + t * 0.2f, y = v * 7.0f;
    int ix = (int)floorf(x), iy = (int)floorf(y);
    float fx = Fr(x) - 0.5f - (Hh(ix, iy, 81) - 0.5f) * 0.3f, fy = Fr(y) - 0.5f - (Hh(ix, iy, 82) - 0.5f) * 0.3f;
    float seed = (Hh(ix, iy, 83) > 0.35f) ? bSm(0.11f, 0.08f, bLen(fx * 1.0f, fy * 0.55f)) : 0.0f;
    r = bMix(r, 0.05f, seed); g = bMix(g, 0.02f, seed); b = bMix(b, 0.02f, seed);
    float white = bSm(0.17f, 0.15f, rm) * bSm(0.10f, 0.13f, rm);
    float rind = bSm(0.11f, 0.09f, rm);
    float stripe = 0.7f + 0.3f * sinf(u * 18.0f + sinf(v * 6.0f) * 2.0f);
    r = bMix(r, 0.95f, white); g = bMix(g, 0.95f, white); b = bMix(b, 0.8f, white);
    r = bMix(r, 0.05f, rind); g = bMix(g, 0.40f * stripe, rind); b = bMix(b, 0.10f, rind);
}
static void NChocolate(float u, float v, float t, float& r, float& g, float& b) {
    float gloss = 0.5f + 0.5f * sinf(u * 5.0f + v * 3.0f - t * 0.8f);
    r = 0.25f + 0.06f * gloss; g = 0.10f + 0.03f * gloss; b = 0.04f + 0.01f * gloss;
    float x = u * 7.0f; int ci = (int)floorf(x); float fx = (Fr(x) - 0.5f) / 7.0f;
    float h = Hh(ci, 0, 71);
    float len = 0.25f + 0.55f * (0.5f + 0.5f * sinf(t * 0.8f + h * 12.0f));
    float d = bCap(fx, v, 0.0f, -0.1f, 0.0f, len, 0.028f);
    float c = bMax(bSm(0.004f, -0.004f, d), bSm(0.12f, 0.10f, v + 0.015f * sinf(u * 30.0f + t)));
    float hl = 0.8f + 0.2f * bSm(0.0f, 0.5f, 1.0f - fabsf(fx) * 30.0f);
    r = bMix(r, 0.95f * hl, c); g = bMix(g, 0.60f * hl, c); b = bMix(b, 0.10f * hl, c);
}
static void NInvaders(float u, float v, float t, float& r, float& g, float& b) {
    static const uint8_t A[8] = {0x18, 0x3C, 0x7E, 0xDB, 0xFF, 0x24, 0x5A, 0xA5};
    static const uint8_t B[8] = {0x18, 0x3C, 0x7E, 0xDB, 0xFF, 0x5A, 0x81, 0x42};
    const float N = 4.0f;
    float x = u * N + 0.15f * sinf(t * 0.8f), y = v * N;
    int ix = (int)floorf(x), iy = (int)floorf(y);
    int lx = (int)floorf((Fr(x)) * 10.0f) - 1, ly = (int)floorf((Fr(y)) * 10.0f) - 1;
    r = g = b = 0.02f;
    if (lx >= 0 && lx < 8 && ly >= 0 && ly < 8) {
        const uint8_t* bm = (((int)floorf(t * 2.0f) + ix + iy) & 1) ? A : B;
        if ((bm[ly] >> (7 - lx)) & 1) Hsv(Hh(iy, 0, 91) + t * 0.05f, 0.9f, 1.0f, r, g, b);
    }
}
static void NRaceFlag(float u, float v, float t, float& r, float& g, float& b) {
    float uu = u + 0.05f * sinf(v * 7.0f - t * 3.5f), vv = v + 0.03f * sinf(u * 9.0f - t * 3.0f);
    int cx = (int)floorf(uu * 8.0f), cy = (int)floorf(vv * 8.0f);
    float shade = 0.78f + 0.22f * cosf(v * 7.0f - t * 3.5f + u * 3.0f);
    float c = (((cx + cy) & 1) ? 0.96f : 0.04f) * shade;
    r = c; g = c; b = c;
}
static void NCamo(float u, float v, float t, float& r, float& g, float& b) {
    float n1 = bFbm(u * 3.0f + t * 0.04f, v * 3.0f), n2 = bFbm(u * 4.0f + 5.0f, v * 4.0f + t * 0.05f), n3 = bFbm(u * 5.0f + 9.0f - t * 0.03f, v * 5.0f + 3.0f);
    r = 0.55f; g = 0.50f; b = 0.32f;
    float m1 = bSm(0.50f, 0.52f, n1); r = bMix(r, 0.30f, m1); g = bMix(g, 0.36f, m1); b = bMix(b, 0.18f, m1);
    float m2 = bSm(0.55f, 0.57f, n2); r = bMix(r, 0.25f, m2); g = bMix(g, 0.17f, m2); b = bMix(b, 0.08f, m2);
    float m3 = bSm(0.58f, 0.60f, n3); r = bMix(r, 0.10f, m3); g = bMix(g, 0.16f, m3); b = bMix(b, 0.08f, m3);
}
static void NTieDye(float u, float v, float t, float& r, float& g, float& b) {
    float x = u - 0.5f, y = v - 0.5f, rr = bLen(x, y), ang = atan2f(y, x);
    float h = ang / kTau * 3.0f + rr * 2.2f + 0.4f * bFbm(u * 4.0f, v * 4.0f + t * 0.2f) + t * 0.08f;
    Hsv(h, 0.8f, 1.0f, r, g, b);
    float fab = 0.92f + 0.08f * sinf(u * 160.0f) * sinf(v * 160.0f);
    r *= fab; g *= fab; b *= fab;
}
static void NSoapBubbles(float u, float v, float t, float& r, float& g, float& b) {
    r = 0.03f + 0.05f * v; g = 0.06f + 0.10f * v; b = 0.16f + 0.2f * v;
    const float COLS = 6.0f;
    int cx = (int)floorf(u * COLS);
    for (int dx = -1; dx <= 1; dx++) {
        int ci = cx + dx;
        for (int j = 0; j < 2; j++) {
            float h = Hh(ci, j, 13);
            float by = 1.15f - Fr(t * (0.04f + 0.08f * Hh(ci, j, 15)) + h) * 1.35f;
            float bx = (ci + 0.2f + 0.6f * Hh(ci, j, 17) + 0.1f * sinf(t * 1.2f + h * 20.0f)) / COLS;
            float rad = 0.04f + 0.07f * Hh(ci, j, 19);
            float dxp = u - bx, dyp = v - by, d = bLen(dxp, dyp);
            if (d > rad * 1.1f) continue;
            float rim = bSm(rad * 0.75f, rad, d) * bSm(rad * 1.08f, rad, d);
            float hr, hg, hb; Hsv(Fr(atan2f(dyp, dxp) / kTau + t * 0.2f + h), 0.6f, 1.0f, hr, hg, hb);
            float k = rim * 0.9f + bSm(rad, 0.0f, d) * 0.06f;
            r += hr * k; g += hg * k; b += hb * k;
            float hl = bSm(rad * 0.22f, 0.0f, bLen(dxp + rad * 0.4f, dyp + rad * 0.4f));
            r += hl * 0.9f; g += hl * 0.9f; b += hl * 0.9f;
        }
    }
}

// ids 59..103
static void NewPixel(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.0f;
    if (id < 70) { NSoda(id - 59, u, v, t, r, g, b); return; }
    switch (id) {
        case 70: NTiger(u, v, t, r, g, b); break;
        case 71: NLeopard(u, v, t, r, g, b); break;
        case 72: NCheetah(u, v, t, r, g, b); break;
        case 73: NZebra(u, v, t, r, g, b); break;
        case 74: NCow(u, v, t, r, g, b); break;
        case 75: NGiraffe(u, v, t, r, g, b); break;
        case 76: NSnake(u, v, t, r, g, b); break;
        case 77: NDalmatian(u, v, t, r, g, b); break;
        case 78: NButterfly(u, v, t, r, g, b); break;
        case 79: NFishScales(u, v, t, r, g, b); break;
        case 80: NParrot(u, v, t, r, g, b); break;
        case 81: NWolfEyes(u, v, t, r, g, b); break;
        case 82: NHoneycomb(u, v, t, r, g, b); break;
        case 83: NFerrari(u, v, t, r, g, b); break;
        case 84: NLambo(u, v, t, r, g, b); break;
        case 85: NTiffany(u, v, t, r, g, b); break;
        case 86: NGucci(u, v, t, r, g, b); break;
        case 87: NGreenCafe(u, v, t, r, g, b); break;
        case 88: NFries(u, v, t, r, g, b); break;
        case 89: NThreeStripes(u, v, t, r, g, b); break;
        case 90: NBarca(u, v, t, r, g, b); break;
        case 91: NGreenWaves(u, v, t, r, g, b); break;
        case 92: NRedCurtain(u, v, t, r, g, b); break;
        case 93: NPurpleGlitch(u, v, t, r, g, b); break;
        case 94: NCandySwirl(u, v, t, r, g, b); break;
        case 95: NPieces(u, v, t, 9.0f, 0.8f, 0, NRgb{1.0f, 0.65f, 0.80f}, r, g, b); break;
        case 96: NWatermelon(u, v, t, r, g, b); break;
        case 97: NChocolate(u, v, t, r, g, b); break;
        case 98: NInvaders(u, v, t, r, g, b); break;
        case 99: NRaceFlag(u, v, t, r, g, b); break;
        case 100: NCamo(u, v, t, r, g, b); break;
        case 101: NTieDye(u, v, t, r, g, b); break;
        case 102: NSoapBubbles(u, v, t, r, g, b); break;
        default: NPieces(u, v, t, 7.0f, 1.1f, 1, NRgb{0.05f, 0.03f, 0.12f}, r, g, b); break;   // 103 Confetti
    }
}

// ---------------- v0.9: more designs for Matrix / Neon / Fire-Ice (ids 104..174) ----------------
// Matrix 104-125 (22) | Neon 126-146 (21) | Fire/Ice 147-174 (28)
// -> Matrix, Neon and Fire/Ice now have 32+ designs each = at least 4 full pages in the menu.
static const int X_MATRIX0 = 104, X_NEON0 = 126, X_FIRE0 = 147, X_END = 175;
static inline bool XIsFireIce(int d) { return d >= X_FIRE0 && d < X_END; }
static inline bool XIsMatrix(int d) { return d >= X_MATRIX0 && d < X_NEON0; }
static const int X_SPACE0 = 175, X_WATER0 = 203, X_GOLD0 = 232, X_GOLD_END = 261, X_EXTRA_END = 384;   // v1.0 Space / Water / Gold, v1.1 Party / Scenes / Soda, v1.2 Animals / Brands / Food&Fun
static inline bool XIsExtra(int d) { return d >= X_SPACE0 && d < X_EXTRA_END; }

static inline float xGl(float d, float k) { return expf(-d * d * k); }                 // glow falloff
static inline float xEdge(float f) { return 0.5f - fabsf(Fr(f) - 0.5f); }               // distance to the nearest integer
static inline void xHue(float& r, float& g, float& b, float h, float in) {
    float hr, hg, hb; Hsv(h, 1.0f, 1.0f, hr, hg, hb);
    r += hr * in; g += hg * in; b += hb * in;
}
static inline float xBell(float f, float c, float w) { float q = (f - c) / w; return expf(-q * q); }
static inline float xBox(float px, float py, float hx, float hy) {
    float qx = fabsf(px) - hx, qy = fabsf(py) - hy;
    return bLen(bMax(qx, 0.0f), bMax(qy, 0.0f)) + bMin(bMax(qx, qy), 0.0f);
}

// ======================= MATRIX (22 new, ids 104..125) =======================
static const char* const MAT_TEXT2[] = {
    "PARSA RSI ON TOP ", "LOS SANTOS NEVER SLEEPS ", "GROVE STREET FOR LIFE ", "ALL WE HAD TO DO WAS FOLLOW THE TRAIN ",
    "RESPECT ", "WELCOME TO SAN ANDREAS ", "HACK THE PLANET ", "SYSTEM ONLINE LOADING TEXTURES ",
    "THE CODE NEVER SLEEPS ", "CJ IS BACK IN TOWN "
};
static const int MAT_NTEXT2 = 10;
// style: 0 falling glyphs, 1 falling text columns, 2 sentences sideways, 3 binary rain, 4 flicker grid,
//        5 rising glyphs, 6 diagonal rain, 7 hex rain, 8 radial wave, 9 binary streams (rows), 10 two-way text columns
// col:   0 solid, 1 rainbow per column, 2 rainbow per cell, 3 rainbow per row, 4 two colours, 5 vertical gradient, 6 heat, 7 whole-car rainbow
struct MXCfg { uint8_t style, col; float r, g, b, r2, g2, b2; };
static const MXCfg MXC[22] = {
    {0, 0, 1.00f, 0.80f, 0.15f, 0, 0, 0},              // 104 gold rain
    {2, 0, 0.10f, 0.95f, 1.00f, 0, 0, 0},              // 105 cyan sentences
    {3, 0, 0.70f, 0.30f, 1.00f, 0, 0, 0},              // 106 purple binary
    {1, 0, 1.00f, 0.50f, 0.08f, 0, 0, 0},              // 107 orange text columns
    {4, 0, 1.00f, 1.00f, 1.00f, 0, 0, 0},              // 108 white flicker
    {0, 0, 1.00f, 0.30f, 0.70f, 0, 0, 0},              // 109 pink rain
    {5, 0, 0.10f, 1.00f, 0.25f, 0, 0, 0},              // 110 rising green
    {5, 1, 1.00f, 1.00f, 1.00f, 0, 0, 0},              // 111 rising rainbow
    {6, 0, 0.10f, 0.90f, 1.00f, 0, 0, 0},              // 112 diagonal cyan
    {6, 2, 1.00f, 1.00f, 1.00f, 0, 0, 0},              // 113 diagonal rainbow
    {7, 0, 0.15f, 1.00f, 0.30f, 0, 0, 0},              // 114 hex green
    {7, 0, 1.00f, 0.10f, 0.10f, 0, 0, 0},              // 115 hex red
    {8, 7, 1.00f, 1.00f, 1.00f, 0, 0, 0},              // 116 radial rainbow
    {8, 0, 0.20f, 0.45f, 1.00f, 0, 0, 0},              // 117 radial blue
    {9, 0, 1.00f, 0.78f, 0.12f, 0, 0, 0},              // 118 binary streams gold
    {9, 0, 0.10f, 0.95f, 1.00f, 0, 0, 0},              // 119 binary streams cyan
    {10, 0, 0.15f, 1.00f, 0.30f, 0, 0, 0},             // 120 two-way green
    {10, 4, 1.00f, 0.10f, 0.90f, 0.10f, 0.90f, 1.00f}, // 121 two-way neon (magenta / cyan)
    {0, 6, 1.00f, 0.50f, 0.05f, 0, 0, 0},              // 122 fire code
    {1, 5, 0.85f, 1.00f, 1.00f, 0.10f, 0.35f, 1.00f},  // 123 ice code (white -> deep blue)
    {0, 5, 1.00f, 0.55f, 0.10f, 0.65f, 0.15f, 1.00f},  // 124 sunset code (orange -> purple)
    {4, 0, 0.55f, 1.00f, 0.05f, 0, 0, 0}               // 125 toxic lime flicker
};
static void MatrixPixelX(int var, float u, float v, float t, float& r, float& g, float& b) {
    const int CW = 6, CH = 8, COLS = 42, ROWS = 32;
    const MXCfg& C = MXC[var];
    int ix = (int)(u * DYN_SIZE), iy = (int)(v * DYN_SIZE);
    int cx = ix / CW, cy = iy / CH;
    if (cx >= COLS || cy >= ROWS || cx < 0 || cy < 0) { r = g = b = 0; return; }
    int lx = ix - cx * CW, ly = iy - cy * CH;
    int style = C.style, salt = var * 37 + 101;
    float br = 0; int gl = 36;
    const float TR = 14.0f;
    if (style == 0 || style == 1 || style == 3 || style == 5 || style == 6 || style == 7) {
        int key = cx, pos = cy;
        if (style == 5) pos = ROWS - 1 - cy;          // streams rise
        if (style == 6) key = cx + (cy >> 1);         // streams run along diagonals
        for (int s = 0; s < 2; s++) {
            float sp = 0.25f + 0.5f * Hh(key, 1 + s * 20, salt);
            float head = Fr(t * sp * 0.45f + Hh(key, 7 + s * 20, salt)) * (ROWS + TR);
            float d = head - pos;
            if (d < 0 || d >= TR) continue;
            float k = powf(1.0f - d / TR, 1.5f);
            if (k > br) {
                br = k;
                int tick = (int)(t * (d < 1 ? 14.0f : 2.5f) + Hh(cx, cy, 5 + salt) * 6.0f) + s;
                float hv = Hh(cx, cy, tick + salt);
                if (style == 1) gl = -1;
                else if (style == 3) gl = hv > 0.5f ? 1 : 0;
                else if (style == 7) gl = (int)(hv * 16.0f) % 16;
                else gl = (int)(hv * 36.0f) % 36;
                if (d < 1.0f) br = 1.25f;
            }
        }
        if (style == 1) {
            const char* tx = MAT_TEXT2[(int)(Hh(key, 2, salt) * MAT_NTEXT2) % MAT_NTEXT2];
            int len = (int)strlen(tx);
            gl = MatCharIdx(tx[(pos + (int)(Hh(key, 3, salt) * 50.0f)) % len]);
            br = bMax(br, 0.22f);
        }
    } else if (style == 2) {
        if (cy & 1) { r = g = b = 0; return; }
        int line = cy >> 1;
        const char* tx = MAT_TEXT2[(int)(Hh(line, 4, salt) * MAT_NTEXT2) % MAT_NTEXT2];
        int len = (int)strlen(tx);
        float sp = 2.0f + 3.0f * Hh(line, 5, salt);
        int off = (int)floorf(t * sp) * ((line & 1) ? 1 : -1);
        gl = MatCharIdx(tx[(((cx + off + (int)(Hh(line, 6, salt) * 40.0f)) % len) + len) % len]);
        br = 0.3f + 0.7f * (0.5f + 0.5f * sinf(cx * 0.22f - t * 2.2f + line * 0.9f));
    } else if (style == 4) {
        float ph = Hh(cx, cy, 9 + salt);
        gl = (int)(Hh(cx, cy, (int)(t * 1.6f + ph * 5.0f) + salt) * 36.0f) % 36;
        float w = 0.5f + 0.5f * sinf(t * 1.3f + cx * 0.33f + cy * 0.21f + ph * 6.0f);
        br = 0.12f + 0.88f * bSm(0.45f, 1.0f, w);
        if (Hh(cx, cy, (int)(t * 6.0f) + salt) > 0.97f) br = 1.2f;
    } else if (style == 8) {
        float dx = cx - COLS * 0.5f, dy = (cy - ROWS * 0.5f) * 1.3f;
        float dist = sqrtf(dx * dx + dy * dy);
        float w = 0.5f + 0.5f * sinf(dist * 0.45f - t * 3.0f);
        br = 0.08f + 0.92f * bSm(0.55f, 1.0f, w);
        gl = (int)(Hh(cx, cy, (int)(t * 1.5f + Hh(cx, cy, 9) * 5.0f) + salt) * 36.0f) % 36;
    } else if (style == 9) {
        int dir = (cy & 1) ? 1 : -1;
        float sp = 3.0f + 5.0f * Hh(cy, 8, salt);
        int off = (int)floorf(t * sp) * dir;
        gl = Hh(cx + off + 100, cy, 21 + salt) > 0.5f ? 1 : 0;
        float k = Fr(cx / 14.0f - dir * t * 0.35f + Hh(cy, 3, salt));
        br = 0.15f + 0.85f * k * k;
    } else {   // 10: two-way text columns
        int dir = (cx & 1) ? 1 : -1;
        const char* tx = MAT_TEXT2[(int)(Hh(cx, 2, salt) * MAT_NTEXT2) % MAT_NTEXT2];
        int len = (int)strlen(tx);
        float sp = 1.5f + 3.0f * Hh(cx, 5, salt);
        int off = (int)floorf(t * sp) * dir;
        gl = MatCharIdx(tx[(((cy + off + (int)(Hh(cx, 3, salt) * 50.0f)) % len) + len) % len]);
        br = 0.3f + 0.7f * (0.5f + 0.5f * sinf(cy * 0.45f - dir * t * 2.4f + cx * 0.7f));
    }
    if (br <= 0 || gl < 0 || !MatBit(gl, lx, ly)) { r = g = b = 0; return; }
    float cr, cg, cb;
    float kk = bMin(br, 1.0f);
    switch (C.col) {
        case 1: Hsv(cx / (float)COLS + t * 0.15f, 1.0f, 1.0f, cr, cg, cb); break;
        case 2: Hsv(Hh(cx, cy, 13) + t * 0.08f, 1.0f, 1.0f, cr, cg, cb); break;
        case 3: Hsv((cy >> 1) / 16.0f + t * 0.12f, 1.0f, 1.0f, cr, cg, cb); break;
        case 4: if (Hh(cx, 12, salt) > 0.5f) { cr = C.r; cg = C.g; cb = C.b; } else { cr = C.r2; cg = C.g2; cb = C.b2; } break;
        case 5: { float k = cy / (float)(ROWS - 1); cr = bMix(C.r, C.r2, k); cg = bMix(C.g, C.g2, k); cb = bMix(C.b, C.b2, k); break; }
        case 6: cr = 1.0f; cg = 0.12f + 0.75f * kk * kk; cb = 0.02f + 0.15f * kk * kk * kk; break;
        case 7: Hsv(t * 0.1f, 1.0f, 1.0f, cr, cg, cb); break;
        default: cr = C.r; cg = C.g; cb = C.b; break;
    }
    float hi = Cl((br - 0.85f) * 2.5f) * 0.7f;
    r = cr * kk + hi; g = cg * kk + hi; b = cb * kk + hi;
}

// ======================= NEON (21 new, ids 126..146) =======================
static void XNeon(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.02f;
    float x = u - 0.5f, y = v - 0.5f;
    switch (id) {
    case 0: {   // Neon tunnel
        float m = bMax(fabsf(x), fabsf(y)) * 2.0f + 0.02f;
        float z = 0.35f / m;
        float q = Fr(z - t * 0.7f) - 0.5f;
        float fade = bMin(1.0f, m * 2.5f);
        xHue(r, g, b, z * 0.12f + t * 0.1f, xGl(q, 70.0f) * fade * 1.3f);
        xHue(r, g, b, 0.55f + t * 0.1f, xGl(fabsf(x) - fabsf(y), 600.0f) * 0.5f * fade);
        break;
    }
    case 1: {   // Neon triangles
        float d = bMin(bMin(xEdge(u * 6.0f), xEdge(v * 6.0f)), xEdge((u + v) * 6.0f));
        float in = xGl(d, 260.0f) * (0.7f + 0.3f * sinf(t * 3.0f + (u + v) * 8.0f));
        xHue(r, g, b, (u + v) * 0.5f + t * 0.1f, in);
        int ci = (int)floorf(u * 6.0f), cj = (int)floorf(v * 6.0f);
        int tri = (Fr(u * 6.0f) + Fr(v * 6.0f) > 1.0f) ? 1 : 0;
        if (Hh(ci, cj + tri * 7, (int)(t * 1.5f)) > 0.85f) xHue(r, g, b, Hh(ci, cj, tri) + t * 0.1f, 0.3f);
        break;
    }
    case 2: {   // Neon hexagons
        float px = u * 6.0f, py = v * 6.0f;
        float ax = nMod(px, 1.0f) - 0.5f, ay = nMod(py, 1.732f) - 0.866f;
        float bx = nMod(px - 0.5f, 1.0f) - 0.5f, by = nMod(py - 0.866f, 1.732f) - 0.866f;
        bool useA = ax * ax + ay * ay < bx * bx + by * by;
        float gx = useA ? ax : bx, gy = useA ? ay : by;
        float hd = bMax(fabsf(gx) * 0.5f + fabsf(gy) * 0.866f, fabsf(gx));
        int id2 = useA ? ((int)floorf(px) + 31 * (int)floorf(py / 1.732f)) : (1000 + (int)floorf(px - 0.5f) + 31 * (int)floorf((py - 0.866f) / 1.732f));
        float h = Hh(id2, 3);
        float pulse = 0.5f + 0.5f * sinf(t * 2.0f + h * 6.28f);
        xHue(r, g, b, h * 0.6f + t * 0.05f, xGl(0.5f - hd, 900.0f) * 1.1f + 0.14f * pulse * bSm(0.5f, 0.1f, hd));
        break;
    }
    case 3: {   // Neon rain
        const float N = 28.0f;
        int col = (int)(u * N);
        float fx = u * N - col - 0.5f;
        float h = Hh(col, 4), sp = 0.3f + 0.6f * Hh(col, 5);
        float head = Fr(t * sp + h);
        float d = Fr(head - v);
        float in = (d < 0.5f ? expf(-d * 7.0f) : 0.0f) * expf(-fx * fx * 70.0f);
        if (d < 0.02f) in += 0.6f * expf(-fx * fx * 40.0f);
        xHue(r, g, b, Hh(col, 6) * 0.7f + t * 0.05f, in);
        break;
    }
    case 4: {   // Neon spider web
        float rr = bLen(x, y) + 1e-4f, ang = atan2f(y, x);
        float dsp = rr * xEdge(ang / kTau * 12.0f) * kTau / 12.0f;
        float pul = 0.55f + 0.45f * sinf(rr * 30.0f - t * 4.0f);
        float sq = sqrtf(rr);
        float drg = xEdge(sq * 7.0f) / 7.0f * 2.0f * sq;
        xHue(r, g, b, rr * 0.8f + t * 0.1f, xGl(dsp, 1200.0f) * pul + xGl(drg, 1500.0f) * 0.9f);
        break;
    }
    case 5: {   // Neon zigzag
        float f = v * 6.0f + fabsf(Fr(u * 5.0f) - 0.5f) * 3.0f - t * 0.6f;
        float d = xEdge(f) / 6.0f;
        xHue(r, g, b, floorf(f + 0.5f) * 0.13f + t * 0.1f, xGl(d, 1800.0f) * (0.8f + 0.2f * sinf(t * 5.0f + u * 10.0f)));
        break;
    }
    case 6: {   // Neon sine waves
        for (int i = 0; i < 5; i++) {
            float yy = 0.5f + (0.2f + 0.08f * sinf(t * 0.7f + i)) * sinf(u * (5.0f + i) + t * (1.0f + 0.4f * i) + i * 1.3f);
            float d = fabsf(v - yy);
            xHue(r, g, b, i * 0.18f + t * 0.08f, xGl(d, 2500.0f) * 0.9f + xGl(d, 150.0f) * 0.12f);
        }
        break;
    }
    case 7: {   // Neon diamonds
        float fu = u * 4.0f, fv = v * 4.0f;
        float px = Fr(fu) - 0.5f, py = Fr(fv) - 0.5f;
        float h = Hh((int)floorf(fu), (int)floorf(fv), 5);
        float m = fabsf(px) + fabsf(py);
        float q = Fr(m * 3.0f - t * 0.8f * (0.6f + h)) - 0.5f;
        xHue(r, g, b, h * 0.7f + t * 0.1f + m * 0.3f, xGl(q, 60.0f) * bSm(0.55f, 0.2f, m) * 1.2f + xGl(m - 0.5f, 400.0f) * 0.4f);
        break;
    }
    case 8: {   // Neon circles
        float fu = u * 5.0f, fv = v * 5.0f;
        int ci = (int)floorf(fu), cj = (int)floorf(fv);
        float h = Hh(ci, cj, 8);
        float px = Fr(fu) - 0.5f, py = Fr(fv) - 0.5f;
        float rad = 0.25f + 0.15f * sinf(t * 2.0f + h * 6.28f);
        float rr = bLen(px, py);
        xHue(r, g, b, h + t * 0.07f, xGl(rr - rad, 700.0f) * 1.1f + xGl(rr, 300.0f) * 0.25f * (0.5f + 0.5f * sinf(t * 3.0f + h * 9.0f)));
        break;
    }
    case 9: {   // Neon DNA
        float ph = u * 9.0f - t * 3.0f;
        float amp = 0.26f;
        float y1 = 0.5f + amp * sinf(ph), y2 = 0.5f - amp * sinf(ph);
        float c = cosf(ph);
        float a1 = 0.45f + 0.55f * Cl(c * 0.5f + 0.5f), a2 = 0.45f + 0.55f * Cl(-c * 0.5f + 0.5f);
        xHue(r, g, b, 0.9f, xGl(v - y1, 3000.0f) * a1 * 1.2f);
        xHue(r, g, b, 0.5f, xGl(v - y2, 3000.0f) * a2 * 1.2f);
        float fx = Fr(u * 14.0f) - 0.5f;
        float lo = bMin(y1, y2), hi = bMax(y1, y2);
        if (v > lo && v < hi) xHue(r, g, b, 0.15f + 0.1f * sinf(t + u * 6.0f), xGl(fx, 900.0f) * 0.7f);
        break;
    }
    case 10: {  // Neon scan lines
        float bar = xGl(Fr(v * 3.0f - t * 0.4f) - 0.5f, 40.0f);
        float lines = Fr(v * 90.0f) < 0.45f ? 1.0f : 0.55f;
        float fl = 0.85f + 0.15f * Hh((int)(t * 20.0f), 1);
        xHue(r, g, b, u * 0.3f + t * 0.1f + v * 0.2f, (0.12f + 0.9f * bar) * lines * fl);
        break;
    }
    case 11: {  // Neon sparks
        const float N = 18.0f;
        int cx = (int)floorf(u * N), cy = (int)floorf(v * N);
        float acc = 0.0f, hue = 0.0f;
        for (int j = 0; j < 2; j++) {
            int cyy = cy - j;                       // a spark leaves a short tail downwards
            float h = Hh(cx, cyy, (int)(t * 2.0f) + 40);
            if (h <= 0.82f) continue;
            float ox = 0.2f + 0.6f * Hh(cx, cyy, 3), oy = 0.2f + 0.6f * Hh(cx, cyy, 4);
            float dx = u * N - cx - ox, dy = v * N - cyy - oy;
            float k = j == 0 ? 1.0f : 0.35f;
            acc += xGl(bLen(dx, dy * (j ? 0.5f : 1.0f)), 55.0f) * k;
            hue = Hh(cx, cyy, 6);
        }
        xHue(r, g, b, hue + t * 0.1f, acc * 1.3f);
        break;
    }
    case 12: {  // Neon plus signs
        float fu = u * 5.0f, fv = v * 5.0f;
        int ci = (int)floorf(fu), cj = (int)floorf(fv);
        float h = Hh(ci, cj, 12);
        float px = Fr(fu) - 0.5f, py = Fr(fv) - 0.5f;
        float a = t * (0.5f + h) * ((ci + cj) & 1 ? 1.0f : -1.0f);
        float ca = cosf(a), sa = sinf(a);
        float qx = px * ca - py * sa, qy = px * sa + py * ca;
        float d = bMin(xBox(qx, qy, 0.3f, 0.07f), xBox(qx, qy, 0.07f, 0.3f));
        xHue(r, g, b, h + t * 0.08f, xGl(d, 900.0f) * 1.1f + (d < 0.0f ? 0.2f : 0.0f));
        break;
    }
    case 13: {  // Neon vortex
        float rr = bLen(x, y) + 1e-4f, ang = atan2f(y, x);
        float s = ang / kTau * 3.0f + logf(rr * 4.0f + 1.0f) * 2.2f - t * 0.5f;
        float q = Fr(s) - 0.5f;
        xHue(r, g, b, rr + t * 0.1f + ang / kTau, xGl(q, 30.0f) * bMin(1.0f, rr * 4.0f));
        float core = xGl(rr, 200.0f) * 0.8f;
        r += core; g += core; b += core;
        break;
    }
    case 14: {  // Neon checker
        int ci = (int)floorf(u * 6.0f), cj = (int)floorf(v * 6.0f);
        float edge = bMin(xEdge(u * 6.0f), xEdge(v * 6.0f));
        float hue = ci * 0.1f + cj * 0.07f + t * 0.08f;
        xHue(r, g, b, hue, xGl(edge, 160.0f) * 0.9f);
        if ((ci + cj) & 1) xHue(r, g, b, hue + 0.3f, 0.18f * (0.5f + 0.5f * sinf(t * 2.0f + (ci + cj) * 0.8f)));
        break;
    }
    case 15: {  // Neon bars
        float f = u * 8.0f - t * 0.8f;
        int idx = (int)floorf(f);
        float fx = Fr(f);
        float hgt = 0.3f + 0.6f * (0.5f + 0.5f * sinf(t * 2.0f + idx * 1.3f));
        float top = 1.0f - hgt;
        float hue = idx * 0.12f + t * 0.05f;
        if (fx > 0.1f && fx < 0.9f) {
            if (v > top) xHue(r, g, b, hue, 0.2f + 0.2f * (v - top) / hgt);
            xHue(r, g, b, hue, xGl(v - top, 900.0f) * 1.2f);
        }
        xHue(r, g, b, hue, xGl(fx - 0.1f, 1200.0f) * 0.5f * (v > top ? 1.0f : 0.0f) + xGl(fx - 0.9f, 1200.0f) * 0.5f * (v > top ? 1.0f : 0.0f));
        break;
    }
    case 16: {  // Neon road
        if (y > 0.0f) {
            float yy = y + 0.012f, z = 0.2f / yy;
            float d1 = xEdge(x * z * 5.0f) / (z * 5.0f);
            float d2 = xEdge(z * 2.0f - t * 1.2f) * yy * yy / 0.4f;
            float in = (xGl(d1, 5000.0f) + xGl(d2, 5000.0f)) * bMin(1.0f, yy * 5.0f);
            xHue(r, g, b, 0.83f + 0.12f * sinf(t + z * 0.5f), in * 1.2f);
        } else {
            float sky = 0.04f + 0.1f * (1.0f + y * 2.0f);
            r += sky * 0.6f; b += sky;
            if (Hh((int)(u * 60.0f), (int)(v * 60.0f), 9) > 0.985f) { float tw = 0.5f + 0.5f * sinf(t * 4.0f + u * 50.0f); r += tw; g += tw; b += tw; }
        }
        break;
    }
    case 17: {  // Neon ripples from drops
        float fu = u * 3.0f, fv = v * 3.0f;
        int ci = (int)floorf(fu), cj = (int)floorf(fv);
        float h = Hh(ci, cj, 17);
        float px = Fr(fu) - 0.5f, py = Fr(fv) - 0.5f;
        float rr = bLen(px, py);
        for (int k = 0; k < 2; k++) {
            float ph = Fr(t * 0.4f + h - k * 0.18f);
            xHue(r, g, b, h + t * 0.07f + k * 0.08f, xGl(rr - ph * 0.6f, 600.0f) * (1.0f - ph) * (k ? 0.6f : 1.1f));
        }
        break;
    }
    case 18: {  // Neon heartbeat
        float f = Fr(u * 2.0f);
        float a = 0.05f * xBell(f, 0.2f, 0.04f) + 0.30f * xBell(f, 0.42f, 0.012f) - 0.08f * xBell(f, 0.38f, 0.012f)
                - 0.07f * xBell(f, 0.46f, 0.014f) + 0.08f * xBell(f, 0.65f, 0.05f);
        float headX = Fr(t * 0.35f);
        float tail = expf(-Fr(headX - u) * 3.0f);
        for (int row = 0; row < 2; row++) {
            float yy = (row ? 0.74f : 0.3f) - a * (row ? 0.8f : 1.0f);
            float d = fabsf(v - yy);
            xHue(r, g, b, row ? 0.5f : 0.95f, (xGl(d, 3500.0f) * 1.1f + xGl(d, 200.0f) * 0.1f) * (0.2f + 0.8f * tail));
        }
        float gr = bMin(xEdge(u * 20.0f), xEdge(v * 20.0f));
        r += 0.02f * xGl(gr, 3000.0f); g += 0.07f * xGl(gr, 3000.0f); b += 0.03f * xGl(gr, 3000.0f);
        break;
    }
    case 19: {  // Neon fireworks
        float fu = u * 2.0f, fv = v * 2.0f;
        int ci = (int)floorf(fu), cj = (int)floorf(fv);
        float h = Hh(ci, cj, 19);
        float px = Fr(fu) - 0.5f, py = Fr(fv) - 0.5f;
        float rr = bLen(px, py), ang = atan2f(py, px);
        float ph = Fr(t * 0.35f + h);
        float ray = powf(0.5f + 0.5f * cosf(ang * 14.0f + h * 6.0f), 6.0f);
        float in = xGl(rr - ph * 0.5f, 500.0f) * ray * powf(1.0f - ph, 1.2f);
        in += xGl(rr - ph * 0.3f, 500.0f) * (1.0f - ray) * 0.4f * (1.0f - ph);
        xHue(r, g, b, h + ph * 0.3f, in * 1.4f);
        break;
    }
    default: {  // 20: Neon marquee
        float dir = 1.0f;
        for (int i = 0; i < 8; i++) {
            if (v * 8.0f < i || v * 8.0f >= i + 1) continue;
            dir = (i & 1) ? 1.0f : -1.0f;
            float f = u * 16.0f - dir * t * 3.0f;
            int bulb = (int)floorf(f);
            float fx = Fr(f) - 0.5f, fy = Fr(v * 8.0f) - 0.5f;
            bool on = ((((bulb + i) % 3) + 3) % 3) == 0;
            xHue(r, g, b, i * 0.12f + t * 0.05f, expf(-(fx * fx * 14.0f + fy * fy * 16.0f)) * (on ? 1.2f : 0.2f));
        }
        break;
    }
    }
}

// ======================= FIRE / ICE (28 new, ids 147..174; drawn at 128x128 and doubled) =======================
// flame colour ramps: f = intensity 0..~1.5
static void xHeat(float f, int pal, float& r, float& g, float& b) {
    switch (pal) {
        case 1: b = Cl(f * 2.2f); g = Cl(f * 1.7f - 0.45f) * 0.9f; r = Cl(f * 1.6f - 1.25f); break;           // blue
        case 2: g = Cl(f * 2.0f); r = Cl(f * 1.6f - 1.1f) * 0.8f; b = Cl(f * 1.2f - 1.0f) * 0.4f; break;     // toxic green
        case 3: r = Cl(f * 1.4f - 0.1f) * 0.7f; b = Cl(f * 2.0f); g = Cl(f * 1.4f - 1.15f); break;           // purple
        case 4: r = Cl(f * 3.0f); g = Cl(f * 3.0f - 0.8f); b = Cl(f * 3.0f - 1.9f); break;                   // white hot
        case 6: b = Cl(0.35f + f); g = Cl(f * 1.2f); r = Cl(f * 1.5f - 0.6f); break;                         // ice
        default: r = Cl(f * 2.0f); g = Cl(f * 2.0f - 0.7f); b = Cl(f * 3.0f - 2.4f); break;                  // classic fire
    }
}
// rising turbulent flame field, strongest at the bottom (v = 1)
static inline float xFl(float u, float v, float t, float sx, float sy, float sp, float bias) {
    float f = bFbm(u * sx, v * sy + t * sp) * 1.15f + (v - 0.5f) * 1.6f + bias;
    return f < 0.0f ? 0.0f : (f > 1.15f ? 1.15f : f);
}
// voronoi: nearest (d1) and second nearest (d2) feature distance in cell units; id = hash of the nearest cell
static void xVor(float px, float py, float& d1, float& d2, float& id) {
    int ix = (int)floorf(px), iy = (int)floorf(py);
    d1 = d2 = 9.0f; id = 0.0f;
    for (int j = -1; j <= 1; j++) for (int i = -1; i <= 1; i++) {
        float fx = ix + i + 0.15f + 0.7f * Hh(ix + i, iy + j, 71), fy = iy + j + 0.15f + 0.7f * Hh(ix + i, iy + j, 72);
        float d = bLen(px - fx, py - fy);
        if (d < d1) { d2 = d1; d1 = d; id = Hh(ix + i, iy + j, 73); }
        else if (d < d2) d2 = d;
    }
}
// a layer of falling / rising round dots (snow, embers)
static float xDots(float u, float v, float n, float vy, float sway, float rad, float seed) {
    float uu = u * n + sway, vv = v * n + vy;
    int ci = (int)floorf(uu), cj = (int)floorf(vv);
    float ox = 0.25f + 0.5f * Hh(ci, cj, (int)seed), oy = 0.25f + 0.5f * Hh(ci, cj, (int)seed + 1);
    if (Hh(ci, cj, (int)seed + 2) < 0.4f) return 0.0f;
    float d = bLen(uu - ci - ox, vv - cj - oy);
    return bSm(rad, rad * 0.25f, d);
}

static void XFireIce(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.0f;
    float x = u * 2.0f - 1.0f, y = v * 2.0f - 1.0f;
    switch (id) {
    // ---------------- FIRE ----------------
    case 0: {   // Campfire
        float m = 1.0f - bSm(0.05f, 0.45f, fabsf(u - 0.5f) * (0.6f + (1.0f - v) * 2.2f));
        float f = xFl(u, v, t, 3.0f, 3.0f, 1.6f, 0.0f) * m * 1.3f;
        xHeat(f, 0, r, g, b);
        float glow = 0.12f * bSm(0.5f, 1.0f, v) * (0.8f + 0.2f * sinf(t * 7.0f));
        r += glow; g += glow * 0.3f;
        break;
    }
    case 1: { float f = xFl(u, v, t, 3.0f, 3.0f, 1.5f, 0.0f); xHeat(f, 1, r, g, b); break; }              // Blue flame
    case 2: { float f = xFl(u, v, t, 3.5f, 3.0f, 1.7f, 0.05f); xHeat(f, 2, r, g, b); break; }             // Toxic green flame
    case 3: { float f = xFl(u, v, t, 3.0f, 2.6f, 1.4f, 0.05f); xHeat(f, 3, r, g, b); break; }             // Purple flame
    case 4: { float f = xFl(u, v, t, 4.0f, 3.5f, 2.6f, 0.1f) * 1.05f; xHeat(f, 4, r, g, b); break; }     // Inferno
    case 5: {   // Rising embers
        float base = 0.22f * bSm(0.45f, 1.0f, v) * (0.6f + 0.8f * bFbm(u * 3.0f, v * 3.0f - t * 0.5f));
        r = base; g = base * 0.25f;
        float s = 0.0f;
        s += xDots(u, v, 22.0f, t * 1.6f, 0.4f * sinf(t + v * 6.0f), 0.28f, 10.0f);
        s += xDots(u, v, 14.0f, t * 1.0f, 0.5f * sinf(t * 0.7f + v * 4.0f), 0.30f, 30.0f);
        s *= 0.5f + 0.5f * sinf(t * 9.0f + u * 40.0f);
        r += s * 1.2f; g += s * (0.4f + 0.3f * v); b += s * 0.05f;
        break;
    }
    case 6: {   // Magma flow
        float n = bFbm(u * 3.0f - t * 0.25f, v * 5.0f + sinf(u * 4.0f + t * 0.4f) * 0.4f);
        float c = xGl(n - 0.5f, 90.0f);
        float crust = 0.08f + 0.1f * bFbm(u * 8.0f, v * 8.0f);
        xHeat(c * 1.2f + 0.05f, 0, r, g, b);
        r += crust * 0.5f; g += crust * 0.1f;
        break;
    }
    case 7: {   // Flame tongues
        float w = 0.5f + 0.5f * sinf(u * 14.0f + sinf(v * 5.0f - t * 3.0f) * 1.5f);
        float f = Cl((v - 0.2f) * 1.8f * (0.4f + 0.6f * w)) * (0.8f + 0.3f * sinf(t * 6.0f + u * 20.0f));
        xHeat(f * 1.3f, 0, r, g, b);
        break;
    }
    case 8: {   // Fire rings
        float rr = bLen(x, y) * 0.8f;
        float f = (0.5f + 0.5f * sinf(rr * 28.0f - t * 3.0f)) * (1.25f - rr * 1.2f) + 0.35f * bFbm(u * 5.0f, v * 5.0f + t);
        xHeat(f, 0, r, g, b);
        break;
    }
    case 9: {   // Fire tornado
        float cx = 0.5f + 0.18f * sinf(v * 7.0f - t * 3.0f);
        float m = 1.0f - bSm(0.04f, 0.33f, fabsf(u - cx));
        float n = bFbm(u * 5.0f + sinf(v * 6.0f - t * 2.0f), v * 4.0f + t * 2.2f);
        float f = (n * 1.1f + 0.25f) * m * 1.5f * (0.35f + 0.65f * v);
        xHeat(f, 0, r, g, b);
        break;
    }
    case 10: {  // Heat haze
        float w = 0.5f + 0.5f * sinf(v * 30.0f - t * 4.0f + sinf(u * 8.0f + t) * 2.0f);
        float f = (0.45f + 0.3f * v) + w * 0.3f;
        xHeat(f, 0, r, g, b);
        break;
    }
    case 11: {  // Glowing coals
        float d1, d2, hid;
        xVor(u * 7.0f, v * 7.0f, d1, d2, hid);
        float pulse = 0.5f + 0.5f * sinf(t * 1.5f + hid * 6.28f);
        float f = (0.25f + 0.9f * pulse) * bSm(0.6f, 0.05f, d1) * bSm(0.0f, 0.12f, d2 - d1);
        xHeat(f, 0, r, g, b);
        float edge = 0.05f * bFbm(u * 9.0f, v * 9.0f);
        r += edge; g += edge * 0.3f;
        break;
    }
    case 12: {  // Phoenix feathers
        float row = floorf(v * 8.0f);
        float px = Fr(u * 8.0f + ((int)row & 1) * 0.5f) - 0.5f, py = Fr(v * 8.0f) - 0.5f;
        float s = bLen(px, py * 0.9f - 0.1f);
        float body = bSm(0.62f, 0.3f, s);
        float f = (0.55f + 0.45f * sinf(t * 2.0f - v * 6.0f + u * 3.0f)) * (0.35f + 0.9f * body) + 0.15f * (1.0f - v);
        float line = bSm(0.40f, 0.5f, s);
        xHeat(f * (1.0f - 0.55f * line), 0, r, g, b);
        break;
    }
    case 13: {  // Volcano sparks
        float base = bFbm(u * 3.0f, v * 3.0f + t * 0.3f) * bSm(0.55f, 1.0f, v) * 0.9f;
        r = base; g = base * 0.3f;
        float s = 0.0f;
        for (int i = 0; i < 14; i++) {
            for (int tl = 0; tl < 3; tl++) {            // each spark drags a short tail
                float ph = Fr(t * 0.3f + i * 0.0714f + 0.05f * Hh(i, 1) - tl * 0.02f);
                float vx = (Hh(i, 2) - 0.5f) * 1.1f, vy = 0.9f + 0.6f * Hh(i, 3);
                float px = 0.5f + vx * ph, py = 1.0f - (vy * ph * 1.5f - 1.8f * ph * ph);
                float d = bLen(u - px, v - py);
                s += xGl(d, 380.0f) * (1.0f - ph * 0.5f) * (tl == 0 ? 1.0f : 0.4f);
            }
        }
        s = bMin(s, 1.6f);
        r += s; g += s * 0.55f; b += s * 0.1f;
        break;
    }
    // ---------------- ICE ----------------
    case 14: {  // Frost crystals
        float n = bFbm(u * 6.0f, v * 6.0f + t * 0.1f);
        float ridge = 1.0f - fabsf(2.0f * n - 1.0f);
        ridge = ridge * ridge * ridge;
        r = 0.05f + ridge * 0.6f; g = 0.15f + ridge * 0.8f; b = 0.35f + ridge * 0.65f;
        if (Hh((int)(u * 80.0f), (int)(v * 80.0f), (int)(t * 4.0f)) > 0.992f) { r = g = b = 1.0f; }
        break;
    }
    case 15: {  // Snowfall
        float bg = 0.08f + 0.1f * v;
        r = bg * 0.3f; g = bg * 0.5f; b = bg * 1.1f;
        float s = xDots(u, v, 10.0f, -t * 1.0f, 0.3f * sinf(t * 0.8f + v * 5.0f), 0.34f, 10.0f)
                + xDots(u, v, 16.0f, -t * 1.5f, 0.3f * sinf(t * 0.9f + v * 6.0f), 0.30f, 30.0f) * 0.8f
                + xDots(u, v, 26.0f, -t * 2.2f, 0.4f * sinf(t * 1.1f + v * 7.0f), 0.28f, 50.0f) * 0.6f;
        s = bMin(s, 1.0f);
        r += s; g += s; b += s;
        break;
    }
    case 16: {  // Blizzard
        float fog = bFbm(u * 2.0f - t * 0.5f, v * 2.0f) * 0.55f;
        r = 0.10f + fog * 0.5f; g = 0.15f + fog * 0.7f; b = 0.25f + fog * 0.8f;
        float s = xDots(u * 0.5f, v * 3.0f, 26.0f, 0.0f, t * 4.0f, 0.36f, 10.0f)
                + xDots(u * 0.5f + 0.2f, v * 3.0f, 18.0f, 0.0f, t * 3.0f, 0.36f, 30.0f);
        s = bMin(s, 1.0f);
        r += s * 0.9f; g += s * 0.95f; b += s;
        break;
    }
    case 17: {  // Frozen lake cracks
        float d1, d2, hid;
        xVor(u * 5.0f, v * 5.0f, d1, d2, hid);
        float n = bFbm(u * 6.0f, v * 6.0f);
        r = 0.08f + 0.15f * n; g = 0.25f + 0.3f * n; b = 0.45f + 0.35f * n;
        float cr = bSm(0.09f, 0.0f, d2 - d1);
        float pulse = 0.4f + 0.6f * Fr(-t * 0.25f + hid);
        r += cr * 0.75f * pulse; g += cr * 0.9f * pulse; b += cr * pulse;
        break;
    }
    case 18: {  // Icicles
        const float N = 12.0f;
        int col = (int)floorf(u * N);
        float fx = Fr(u * N) - 0.5f;
        float len = 0.25f + 0.5f * Hh(col, 5);
        float bg = 0.07f + 0.1f * bFbm(u * 4.0f, v * 4.0f);
        r = bg * 0.3f; g = bg * 0.6f; b = bg * 1.3f;
        float prof = 0.42f * (1.0f - v / len);
        if (v < len && fabsf(fx) < prof) {
            float sh = 0.55f + 0.45f * (1.0f - fabsf(fx) / (prof + 1e-4f));
            r = 0.35f * sh + 0.4f * (v / len); g = 0.7f * sh + 0.25f * (v / len); b = 0.95f * sh;
            if (fabsf(fx) > prof * 0.8f) { r += 0.25f; g += 0.25f; b += 0.15f; }
        }
        float ph = Fr(t * 0.5f + Hh(col, 7));
        float dy = v - (len + ph * 0.5f), dx = fx;
        float drop = xGl(bLen(dx * 2.0f, dy), 1400.0f) * (1.0f - ph);
        r += drop * 0.7f; g += drop * 0.9f; b += drop;
        break;
    }
    case 19: {  // Glacier layers
        float f = 0.5f + 0.5f * sinf(v * 10.0f + bFbm(u * 3.0f, v * 2.0f + t * 0.1f) * 5.0f + t * 0.3f);
        r = bMix(0.02f, 0.7f, f * f); g = bMix(0.2f, 0.95f, f); b = bMix(0.5f, 1.0f, f);
        break;
    }
    case 20: {  // Snowflakes
        float fu = u * 3.0f, fv = v * 3.0f;
        int ci = (int)floorf(fu), cj = (int)floorf(fv);
        float h = Hh(ci, cj, 20);
        float px = Fr(fu) - 0.5f, py = Fr(fv) - 0.5f;
        float rr = bLen(px, py), ang = atan2f(py, px) + t * (0.2f + 0.3f * h) * ((ci + cj) & 1 ? 1.0f : -1.0f);
        float seg = kTau / 6.0f;
        float a = fabsf(nMod(ang, seg) - seg * 0.5f);
        float qx = rr * cosf(a), qy = rr * sinf(a);
        float sc = 0.8f + 0.5f * h;
        qx /= sc; qy /= sc;
        float d = bMin(bCap(qx, qy, 0.0f, 0.0f, 0.4f, 0.0f, 0.02f),
                  bMin(bCap(qx, qy, 0.16f, 0.0f, 0.27f, 0.11f, 0.014f), bCap(qx, qy, 0.29f, 0.0f, 0.38f, 0.08f, 0.012f)));
        float bg = 0.06f + 0.05f * h;
        r = bg * 0.3f; g = bg * 0.6f; b = bg * 1.4f;
        float in = bSm(0.012f, -0.004f, d) + xGl(d, 700.0f) * 0.4f;
        r += in * 0.85f; g += in * 0.95f; b += in;
        break;
    }
    case 21: {  // Dry ice fog
        float n1 = bFbm(u * 3.0f + t * 0.2f, v * 3.0f - t * 0.1f);
        float n2 = bFbm(u * 5.0f - t * 0.15f, v * 4.0f + t * 0.12f);
        float f = n1 * n2 * 2.2f * (0.4f + 0.8f * v);
        r = 0.02f + f * 0.45f; g = 0.05f + f * 0.8f; b = 0.1f + f * 0.95f;
        break;
    }
    case 22: {  // Cold plasma
        float val = sinf(u * 9.0f + t) + sinf(v * 7.0f - t * 1.2f) + sinf((u + v) * 6.0f + t * 0.8f) + sinf(bLen(u - 0.5f, v - 0.5f) * 14.0f - t);
        float f = 0.5f + 0.25f * val;
        r = Cl(f * f * 1.2f - 0.1f); g = Cl(f * 1.1f); b = Cl(0.4f + f * 0.8f);
        break;
    }
    case 23: {  // Diamond ice
        float a = (u + v) * 6.0f, bq = (u - v) * 6.0f;
        int ia = (int)floorf(a), ib = (int)floorf(bq);
        float sh = 0.3f + 0.5f * Hh(ia, ib, 23);
        float sweep = xGl(Fr((u + v) * 0.7f - t * 0.3f) - 0.5f, 25.0f);
        float edge = xGl(bMin(xEdge(a), xEdge(bq)), 300.0f);
        r = 0.05f + sh * 0.35f + sweep * 0.5f * sh + edge * 0.5f;
        g = 0.2f + sh * 0.6f + sweep * 0.5f * sh + edge * 0.7f;
        b = 0.4f + sh * 0.6f + sweep * 0.4f + edge * 0.9f;
        break;
    }
    case 24: {  // Frozen waves
        float h = 0.5f + 0.25f * sinf(u * 7.0f + t * 0.6f) + 0.15f * sinf(u * 13.0f - t * 0.9f + v * 4.0f) + 0.1f * sinf(v * 9.0f + t * 0.4f);
        float f = Cl(h);
        float cap = bSm(0.72f, 0.9f, f);
        r = 0.03f + f * 0.25f + cap * 0.6f; g = 0.15f + f * 0.5f + cap * 0.5f; b = 0.35f + f * 0.5f + cap * 0.3f;
        break;
    }
    case 25: {  // Blue ice shimmer
        float n = bFbm(u * 4.0f + t * 0.15f, v * 4.0f);
        float c = xGl(bFbm(u * 5.0f - t * 0.2f, v * 5.0f + t * 0.1f) - 0.5f, 30.0f);
        r = 0.05f + n * 0.15f + c * 0.6f; g = 0.2f + n * 0.4f + c * 0.8f; b = 0.45f + n * 0.4f + c;
        if (Hh((int)(u * 70.0f), (int)(v * 70.0f), (int)(t * 5.0f)) > 0.993f) { r = g = b = 1.0f; }
        break;
    }
    // ---------------- BOTH ----------------
    case 26: {  // Fire & ice spiral
        float rr = bLen(x, y) + 1e-4f, ang = atan2f(y, x);
        float s = ang / kTau * 2.0f + rr * 1.5f - t * 0.25f;
        float q = Fr(s);
        float fr, fg, fb;
        if (q < 0.5f) {
            float f = bFbm(u * 4.0f, v * 4.0f + t * 1.5f) * 1.2f + 0.4f;
            xHeat(f, 0, fr, fg, fb);
        } else {
            float f = bFbm(u * 4.0f, v * 4.0f - t * 0.3f) * 0.7f + 0.2f;
            xHeat(f, 6, fr, fg, fb);
        }
        float edge = xGl(fabsf(q - 0.5f) - 0.0f, 900.0f) + xGl(fminf(q, 1.0f - q), 900.0f);
        r = fr + edge * 0.6f; g = fg + edge * 0.6f; b = fb + edge * 0.6f;
        break;
    }
    default: {  // 27: Fire & ice yin-yang
        float a = t * 0.4f, ca = cosf(a), sa = sinf(a);
        float px = x * ca - y * sa, py = x * sa + y * ca;
        float rr = bLen(px, py);
        bool ice;
        if (rr < 0.8f) {
            if (bLen(px, py - 0.4f) < 0.4f) ice = true;
            else if (bLen(px, py + 0.4f) < 0.4f) ice = false;
            else ice = px < 0.0f;
            if (bLen(px, py - 0.4f) < 0.11f) ice = false;
            if (bLen(px, py + 0.4f) < 0.11f) ice = true;
        } else ice = px > 0.0f;
        float fr, fg, fb;
        if (ice) { float f = bFbm(u * 4.0f, v * 4.0f - t * 0.3f) * 0.7f + 0.2f; xHeat(f, 6, fr, fg, fb); }
        else { float f = bFbm(u * 4.0f, v * 4.0f + t * 1.5f) * 1.2f + 0.4f; xHeat(f, 0, fr, fg, fb); }
        float rim = xGl(rr - 0.8f, 600.0f);
        r = fr + rim * 0.5f; g = fg + rim * 0.5f; b = fb + rim * 0.5f;
        break;
    }
    }
}

// ======================= v1.0: SPACE / WATER / GOLD (86 new, ids 175..260; drawn at 128x128 and doubled) =======================
// Space 175-202 (28) | Water 203-231 (29) | Gold 232-260 (29)
// -> Space, Water and Gold now have 32 designs each = at least 4 full pages in the menu.
static const float kPiX = 3.14159265f;

// gold colour ramp: f 0 = dark brown, ~0.7 = gold, 1 = pale yellow
static inline void xGoldRamp(float f, float& r, float& g, float& b) {
    f = Cl(f);
    r = Cl(0.07f + f);
    g = Cl(0.04f + f * f * 0.9f + f * 0.1f);
    b = Cl(f * f * f * 0.75f);
}
// static twinkling stars: n x n grid, one star per cell with some probability
static float xStar(float u, float v, float n, int seed, float t) {
    float uu = u * n, vv = v * n;
    int ci = (int)floorf(uu), cj = (int)floorf(vv);
    float h = Hh(ci, cj, seed);
    if (h < 0.55f) return 0.0f;
    float ox = 0.2f + 0.6f * Hh(ci, cj, seed + 1), oy = 0.2f + 0.6f * Hh(ci, cj, seed + 2);
    float dx = uu - ci - ox, dy = vv - cj - oy;
    float tw = 0.55f + 0.45f * sinf(t * (1.5f + 3.0f * h) + h * 40.0f);
    return expf(-(dx * dx + dy * dy) * 60.0f) * tw * (0.4f + h);
}
static inline void xAddStars(float& r, float& g, float& b, float s) { r += s * 0.9f; g += s * 0.95f; b += s; }
// staggered rows of round scales: distance to the nearest scale centre (cell units, 0..~0.56) and a per-scale random
static void xScaleCell(float u, float v, float n, float& d, float& idc) {
    float uu = u * n, vv = v * n * 2.0f;
    int j0 = (int)floorf(vv);
    d = 9.0f; idc = 0.0f;
    for (int j = j0; j <= j0 + 1; j++) {
        float s = (j & 1) ? 0.5f : 0.0f;
        float ci = floorf(uu - s + 0.5f);
        float dx = uu - (ci + s), dy = (vv - (float)j) * 0.5f;
        float dd = bLen(dx, dy);
        if (dd < d) { d = dd; idc = Hh((int)ci, j, 77); }
    }
}

// ---------------------------------------- SPACE (28) ----------------------------------------
static void XSpace(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.012f;
    float x = u - 0.5f, y = v - 0.5f;
    float st = xStar(u, v, 16.0f, 3, t) + 0.6f * xStar(u, v, 31.0f, 8, t * 1.3f);   // background stars
    switch (id) {
    case 0: {   // Saturn rings
        xAddStars(r, g, b, st);
        float d = bLen(x, y), e = bLen(x, y * 3.4f);
        float ringA = bSm(0.27f, 0.30f, e) * bSm(0.47f, 0.44f, e);
        ringA *= (0.55f + 0.45f * sinf(e * 130.0f - t * 0.6f)) * (1.0f - 0.85f * bSm(0.375f, 0.385f, e) * bSm(0.405f, 0.395f, e));
        float rc = 0.55f + 0.3f * sinf(e * 60.0f);
        if (y < 0.0f && ringA > 0.0f) bPut(r, g, b, 0.9f * rc, 0.75f * rc, 0.5f * rc, ringA * 0.9f);
        float pa = bSm(0.2f, 0.195f, d);
        if (pa > 0.0f) {
            float nz = sqrtf(Cl(1.0f - (d / 0.2f) * (d / 0.2f)));
            float lit = 0.18f + 0.82f * Cl(nz * 0.95f - x * 1.6f - y * 0.9f);
            float band = 0.5f + 0.5f * sinf(y * 55.0f + bVn(x * 8.0f, y * 8.0f + 2.0f) * 4.0f);
            bPut(r, g, b, bMix(0.95f, 0.72f, band) * lit, bMix(0.78f, 0.55f, band) * lit, bMix(0.5f, 0.3f, band) * lit, pa);
        }
        if (y >= 0.0f && ringA > 0.0f) bPut(r, g, b, 0.9f * rc, 0.75f * rc, 0.5f * rc, ringA * 0.9f);
        break;
    }
    case 1: {   // Comet shower
        xAddStars(r, g, b, st * 0.8f);
        float a = u * 0.86f + v * 0.5f, c = -u * 0.5f + v * 0.86f;
        for (int i = 0; i < 6; i++) {
            float sp = 0.18f + 0.14f * Hh(i, 1);
            float ph = Fr(t * sp + Hh(i, 2));
            float ah = -0.15f + 1.7f * ph, c0 = -0.4f + 1.2f * Hh(i, 3);
            float da = ah - a, dc = c - c0;
            float tail = 0.0f;
            if (da > 0.0f) tail = expf(-dc * dc / (0.0003f + 0.002f * da)) * expf(-da * 4.5f);
            float hd = expf(-(da * da + dc * dc) * 1800.0f) * 2.0f;
            r += tail * 0.5f + hd; g += tail * 0.9f + hd; b += tail + hd;
        }
        break;
    }
    case 2: {   // Supernova
        xAddStars(r, g, b, st * 0.6f);
        float d = bLen(x, y), T = Fr(t * 0.16f), rr = T * 0.75f;
        float ang = atan2f(y, x);
        float fil = bFbm(cosf(ang) * 3.0f + 4.0f, sinf(ang) * 3.0f + t * 0.2f);
        float shell = xGl(d - rr * (0.85f + 0.25f * fil), 500.0f) * (1.0f - T);
        float core = xGl(d, 40.0f) * (1.0f - T) * 2.0f;
        float hr, hg, hb;
        xHeat(core + shell * 1.2f, 0, hr, hg, hb);
        r += hr; g += hg; b += hb;
        float ring = xGl(d - rr * 1.05f, 1500.0f) * (1.0f - T);
        r += ring * 0.3f; g += ring * 0.6f; b += ring * 0.95f;
        break;
    }
    case 3: {   // Pulsar beams
        float d = bLen(x, y);
        for (int k = 0; k < 2; k++) {
            float ph = k == 0 ? t * 1.4f : t * 0.9f + 2.0f;
            float cs = cosf(ph), sn = sinf(ph);
            float pxl = x * cs + y * sn, pyl = -x * sn + y * cs;
            float w = 1.0f + fabsf(pxl) * 5.0f;
            float beam = xGl(pyl / w, 2200.0f) * expf(-fabsf(pxl) * 2.5f) * 1.2f;
            if (k == 0) { r += beam * 0.5f; g += beam * 0.9f; b += beam; }
            else { r += beam * 0.9f; g += beam * 0.3f; b += beam * 0.8f; }
        }
        float core = xGl(d, 900.0f) * 2.5f + xGl(d, 80.0f) * 0.5f;
        r += core; g += core; b += core;
        xAddStars(r, g, b, st * 0.5f);
        break;
    }
    case 4: {   // Wormhole
        float d = bLen(x, y) + 0.001f, ang = atan2f(y, x);
        float z = 0.2f / d;
        float q = Fr(z * 1.4f - t * 0.6f + ang / kTau * 3.0f);
        float ring = xGl(q - 0.5f, 18.0f);
        float fade = bSm(0.02f, 0.2f, d);
        xHue(r, g, b, z * 0.15f + t * 0.06f + ang / kTau * 0.3f, ring * fade * 1.1f);
        xHue(r, g, b, z * 0.15f + t * 0.06f + 0.5f, xGl(Fr(ang / kTau * 18.0f + z * 3.0f) - 0.5f, 60.0f) * fade * 0.35f);
        float halo = xGl(d - 0.07f, 1500.0f);
        r += halo; g += halo * 0.9f; b += halo;
        break;
    }
    case 5: {   // Meteor rain
        xAddStars(r, g, b, st * 0.5f);
        const float N = 11.0f;
        float sx = u + v * 0.45f;
        int col = (int)floorf(sx * N);
        float fx = sx * N - col - 0.5f;
        float h = Hh(col, 5), sp = 0.25f + 0.35f * Hh(col, 6);
        float head = Fr(t * sp + h) * 1.5f - 0.2f;
        float dy = head - v;
        if (dy > 0.0f && dy < 0.6f) {
            float in = expf(-fx * fx * (40.0f + dy * 500.0f)) * expf(-dy * 6.0f);
            r += in * 1.2f; g += in * (0.35f + 0.4f * (1.0f - dy)); b += in * 0.1f;
        }
        float hd = expf(-(fx * fx * 50.0f + dy * dy * 3000.0f)) * 1.6f;
        r += hd; g += hd * 0.8f; b += hd * 0.5f;
        break;
    }
    case 6: {   // Planet horizon
        float d = bLen(x, y - 1.75f);
        float atm = bSm(1.52f, 1.35f, d);
        float sun = xGl(bLen(x * 0.7f, y - 0.38f), 35.0f) * (0.8f + 0.2f * sinf(t * 1.5f));
        xAddStars(r, g, b, st * (1.0f - atm));
        r += atm * (0.08f + sun * 1.2f); g += atm * (0.2f + sun * 0.7f); b += atm * (0.45f + sun * 0.2f);
        float surf = bSm(1.352f, 1.34f, d);
        float cl = bFbm(x * 6.0f + t * 0.03f, y * 6.0f);
        bPut(r, g, b, 0.03f + cl * 0.12f + sun * 0.3f, 0.07f + cl * 0.16f + sun * 0.15f, 0.14f + cl * 0.2f, surf);
        float rim = xGl(d - 1.35f, 1500.0f);
        r += rim * (0.6f + sun); g += rim * (0.8f + sun * 0.5f); b += rim;
        break;
    }
    case 7: {   // Cosmic dust
        float n1 = bFbm(u * 3.0f + t * 0.04f, v * 3.0f), n2 = bFbm(u * 5.0f - t * 0.03f + 7.0f, v * 5.0f + 3.0f);
        float a1 = bSm(0.35f, 0.8f, n1), a2 = bSm(0.4f, 0.85f, n2);
        r += a1 * 0.9f + a2 * 0.2f; g += a1 * 0.25f + a2 * 0.55f; b += a1 * 0.2f + a2 * 0.7f;
        float ridge = xGl(n1 - 0.62f, 120.0f);
        r += ridge * 0.5f; g += ridge * 0.35f; b += ridge * 0.2f;
        xAddStars(r, g, b, st * (1.0f - 0.7f * a1));
        break;
    }
    case 8: {   // Shooting stars
        xAddStars(r, g, b, st * 0.9f);
        for (int i = 0; i < 4; i++) {
            float k = t * 0.35f + i * 0.27f;
            int cyc = (int)floorf(k);
            float p = k - cyc;
            if (p > 0.5f) continue;
            float pp = p / 0.5f;
            float x0 = 0.05f + 0.6f * Hh(i, cyc, 5), y0 = 0.05f + 0.5f * Hh(i, cyc, 6);
            float hx = x0 + pp * 0.45f, hy = y0 + pp * 0.27f;
            float rx = u - hx, ry = v - hy;
            float al = -(rx * 0.857f + ry * 0.514f), pe = rx * -0.514f + ry * 0.857f;
            float fade = sinf(pp * kPiX);
            float in = 0.0f;
            if (al > 0.0f) in = expf(-al * 10.0f) * expf(-pe * pe * 30000.0f / (1.0f + al * 20.0f));
            in += expf(-(rx * rx + ry * ry) * 30000.0f) * 1.5f;
            in *= fade;
            r += in * 0.9f; g += in * 0.95f; b += in;
        }
        break;
    }
    case 9: {   // Solar flare
        float cy2 = y;
        float d = bLen(x, cy2), ang = atan2f(cy2, x);
        const float R0 = 0.33f;
        float fl = bFbm(cosf(ang) * 2.5f + 3.0f, sinf(ang) * 2.5f + t * 0.35f);
        float edge = R0 + 0.22f * fl * fl * 2.0f - d;
        float f;
        if (d < R0) {
            float gran = bFbm(x * 14.0f, cy2 * 14.0f + t * 0.5f);
            float limb = sqrtf(Cl(1.0f - (d / R0) * (d / R0)));
            f = 0.55f + 0.6f * gran * limb + 0.1f;
        } else f = Cl(edge * 7.0f) * 0.9f;
        float hr, hg, hb;
        xHeat(f, 0, hr, hg, hb);
        float gl = xGl(d - R0, 60.0f) * 0.5f * (0.85f + 0.15f * sinf(t * 2.0f));
        r += hr + gl; g += hg + gl * 0.45f; b += hb + gl * 0.1f;
        xAddStars(r, g, b, st * 0.6f * bSm(0.45f, 0.7f, d));
        break;
    }
    case 10: {  // Constellations
        float uu = u * 5.0f, vv = v * 5.0f;
        int ci = (int)floorf(uu), cj = (int)floorf(vv);
        float line = 0.0f, dot = 0.0f;
        for (int j = -1; j <= 1; j++) for (int i = -1; i <= 1; i++) {
            int gi = ci + i, gj = cj + j;
            float ax = gi + 0.2f + 0.6f * Hh(gi, gj, 41), ay = gj + 0.2f + 0.6f * Hh(gi, gj, 42);
            dot += expf(-((uu - ax) * (uu - ax) + (vv - ay) * (vv - ay)) * 500.0f) * (0.7f + 0.3f * sinf(t * 2.0f + Hh(gi, gj, 44) * 30.0f));
            if (Hh(gi, gj, 43) > 0.35f) {
                float bx = gi + 1 + 0.2f + 0.6f * Hh(gi + 1, gj, 41), by = gj + 0.2f + 0.6f * Hh(gi + 1, gj, 42);
                line += xGl(bCap(uu, vv, ax, ay, bx, by, 0.0f), 3500.0f) * (0.45f + 0.35f * sinf(t * 2.0f + Hh(gi, gj, 45) * 20.0f));
            }
            if (Hh(gi, gj, 46) > 0.4f) {
                float bx = gi + 0.2f + 0.6f * Hh(gi, gj + 1, 41), by = gj + 1 + 0.2f + 0.6f * Hh(gi, gj + 1, 42);
                line += xGl(bCap(uu, vv, ax, ay, bx, by, 0.0f), 3500.0f) * (0.45f + 0.35f * sinf(t * 2.0f + Hh(gi, gj, 47) * 20.0f));
            }
        }
        float nb = bFbm(u * 3.0f, v * 3.0f) * 0.07f;
        r += dot * 0.95f + line * 0.35f + nb * 0.4f; g += dot * 0.95f + line * 0.55f + nb * 0.3f; b += dot + line * 0.9f + nb;
        break;
    }
    case 11: {  // Orbiting planets
        xAddStars(r, g, b, st * 0.7f);
        float d0 = bLen(x, y);
        float sun = xGl(d0, 900.0f) * 2.2f + xGl(d0, 60.0f) * 0.4f;
        r += sun; g += sun * 0.8f; b += sun * 0.4f;
        for (int i = 0; i < 4; i++) {
            float R = 0.11f + 0.1f * i;
            float oring = xGl(bLen(x, y / 0.5f) - R, 9000.0f) * 0.18f;
            r += oring * 0.6f; g += oring * 0.7f; b += oring;
            float ang = t * (1.4f / (1.0f + i * 0.9f)) + i * 1.9f;
            float px = cosf(ang) * R, py = sinf(ang) * R * 0.5f;
            float pd = bLen(x - px, y - py);
            float pr = 0.012f + 0.006f * i;
            float hr, hg, hb;
            Hsv(0.05f + i * 0.2f, 0.65f, 1.0f, hr, hg, hb);
            bPut(r, g, b, hr, hg, hb, bSm(pr, pr * 0.6f, pd));
            float gl = xGl(pd, 5000.0f) * 0.25f;
            r += hr * gl; g += hg * gl; b += hb * gl;
        }
        break;
    }
    case 12: {  // Alien sky
        r = bMix(0.14f, 0.02f, v); g = bMix(0.02f, 0.26f, v); b = bMix(0.28f, 0.3f, v);
        float rib = xGl(y + 0.12f * sinf(x * 5.0f + t * 0.5f) + 0.05f * sinf(x * 13.0f - t) + 0.1f, 150.0f) * (0.4f + 0.6f * bFbm(u * 6.0f + t * 0.2f, 1.3f));
        g += rib * 0.8f; b += rib * 0.4f;
        xAddStars(r, g, b, st * (1.0f - v) * 1.2f);
        float m1 = bLen(x + 0.18f, y + 0.16f);
        if (m1 < 0.16f) {
            float nz = sqrtf(Cl(1.0f - (m1 / 0.16f) * (m1 / 0.16f)));
            float lit = 0.25f + 0.75f * Cl(nz * 0.9f - (x + 0.18f) * 1.2f - (y + 0.16f) * 0.8f);
            float cr = 1.0f - 0.35f * bSm(0.55f, 0.7f, bVn((x + 0.18f) * 22.0f, (y + 0.16f) * 22.0f));
            bPut(r, g, b, 0.9f * lit * cr, 0.85f * lit * cr, 0.78f * lit * cr, bSm(0.16f, 0.155f, m1));
        }
        float m2 = bLen(x - 0.26f, y - 0.12f);
        if (m2 < 0.085f) {
            float nz = sqrtf(Cl(1.0f - (m2 / 0.085f) * (m2 / 0.085f)));
            float lit = 0.25f + 0.75f * Cl(nz * 0.9f + (x - 0.26f) * 3.0f - (y - 0.12f) * 2.0f);
            bPut(r, g, b, 0.55f * lit, 0.95f * lit, 0.8f * lit, bSm(0.085f, 0.08f, m2));
        }
        break;
    }
    case 13: {  // Asteroid field
        xAddStars(r, g, b, st * 0.7f);
        for (int L = 0; L < 2; L++) {
            float sc = L == 0 ? 3.0f : 5.0f, sp = L == 0 ? 0.25f : 0.5f;
            float uu = u * sc + t * sp, vv = v * sc;
            int ci = (int)floorf(uu), cj = (int)floorf(vv);
            if (Hh(ci, cj, 90 + L) < 0.35f) continue;
            float ox = 0.35f + 0.3f * Hh(ci, cj, 91 + L), oy = 0.35f + 0.3f * Hh(ci, cj, 92 + L);
            float dx = uu - ci - ox, dy = vv - cj - oy;
            float ang = atan2f(dy, dx) + t * (0.3f + Hh(ci, cj, 93));
            float R0 = 0.14f + 0.14f * Hh(ci, cj, 94);
            float rr = R0 * (0.75f + 0.5f * bVn(cosf(ang) * 2.0f + ci * 7.0f + 10.0f, sinf(ang) * 2.0f + cj * 7.0f + 10.0f));
            float d = bLen(dx, dy);
            if (d < rr * 1.05f) {
                float shade = 0.3f + 0.7f * Cl(0.6f - (dx * 0.7f + dy * 0.5f) / rr * 0.5f);
                float cr = 1.0f - 0.4f * bSm(0.6f, 0.75f, bVn(dx * 16.0f + ci * 3.0f + 20.0f, dy * 16.0f + cj * 3.0f + 20.0f));
                float k = shade * cr * (L == 0 ? 1.0f : 0.75f);
                bPut(r, g, b, 0.62f * k, 0.55f * k, 0.48f * k, bSm(rr, rr * 0.9f, d));
            }
        }
        break;
    }
    case 14: {  // Warp speed
        float d = bLen(x, y), a = atan2f(y, x) / kTau + 0.5f;
        const float N = 70.0f;
        int k = (int)floorf(a * N);
        float fx = Fr(a * N) - 0.5f;
        float h = Hh(k, 7), sp = 0.5f + 0.9f * h;
        float head = Fr(t * sp * 0.6f + h) * 1.3f;
        float dd = head - d;
        if (dd > 0.0f && dd < 0.35f) {
            float in = expf(-fx * fx * 60.0f) * expf(-dd * 10.0f) * bSm(0.03f, 0.2f, d);
            xHue(r, g, b, 0.55f + h * 0.2f, in * 1.4f);
            r += in * 0.3f; g += in * 0.3f; b += in * 0.3f;
        }
        float cg = xGl(d, 300.0f) * 0.6f;
        r += cg * 0.5f; g += cg * 0.7f; b += cg;
        break;
    }
    case 15: {  // Red giant
        float d = bLen(x, y);
        const float R0 = 0.3f;
        float d1, d2, vid;
        xVor(x * 9.0f + t * 0.05f + 5.0f, y * 9.0f + 5.0f, d1, d2, vid);
        float gl = xGl(d - R0, 25.0f) * 0.55f;
        r += gl; g += gl * 0.18f; b += gl * 0.05f;
        if (d < R0) {
            float limb = sqrtf(Cl(1.0f - (d / R0) * (d / R0)));
            float cell = 0.55f + 0.35f * (1.0f - bSm(0.0f, 0.7f, d1)) + 0.1f * sinf(t * 1.5f + vid * 30.0f);
            float hr, hg, hb;
            xHeat(cell * (0.45f + 0.7f * limb), 0, hr, hg, hb);
            bPut(r, g, b, hr, hg * 0.8f, hb * 0.5f, bSm(R0, R0 - 0.01f, d));
        }
        xAddStars(r, g, b, st * 0.5f * bSm(0.3f, 0.45f, d));
        break;
    }
    case 16: {  // Milky Way
        float bnd = x * 0.5f + y * 0.87f + 0.07f * sinf(x * 6.0f) + 0.06f * (bFbm(u * 3.0f, v * 3.0f) - 0.5f);
        float dens = xGl(bnd, 22.0f) * (0.45f + 0.8f * bFbm(u * 6.0f + t * 0.01f, v * 6.0f));
        float lane = 1.0f - 0.65f * bSm(0.5f, 0.75f, bFbm(u * 9.0f + 3.0f, v * 9.0f + 1.0f)) * xGl(bnd, 90.0f);
        dens *= lane;
        float halo = xGl(bnd, 6.0f) * 0.12f;
        r += dens * 0.95f; g += dens * 0.8f + halo * 0.4f; b += dens * 0.75f + halo + 0.04f;
        float s2 = xStar(u, v, 26.0f, 5, t) * (0.4f + dens * 2.5f);
        xAddStars(r, g, b, st * 0.8f + s2);
        break;
    }
    case 17: {  // Neutron star
        float d = bLen(x, y) + 1e-4f;
        float phi = t * 1.3f, ax = cosf(phi), ay = sinf(phi);
        float cth = (x * ax + y * ay) / d;
        float s2 = 1.0f - cth * cth;
        float L = d / (s2 + 0.03f);
        float q = Fr(L * 4.5f);
        float fld = xGl(q - 0.5f, 150.0f) * bSm(0.55f, 0.1f, d) * bSm(0.015f, 0.06f, d);
        float jet = xGl(-x * ay + y * ax, 2500.0f) * expf(-fabsf(x * ax + y * ay) * 3.0f);
        r += fld * 0.3f + jet * 0.4f; g += fld * 0.6f + jet * 0.7f; b += fld + jet;
        float core = xGl(d, 1800.0f) * 2.0f + xGl(d, 150.0f) * 0.4f;
        r += core; g += core; b += core;
        xAddStars(r, g, b, st * 0.5f);
        break;
    }
    case 18: {  // Quasar jet
        float wj = 0.015f + 0.1f * fabsf(y);
        float sway = 0.03f * sinf(y * 9.0f - t * 3.0f);
        float jet = expf(-(x - sway) * (x - sway) / (wj * wj)) * (0.35f + 0.65f * bFbm(x * 12.0f, y * 6.0f - t * 2.0f))
                  * bSm(0.0f, 0.1f, fabsf(y)) * (1.0f - bSm(0.3f, 0.5f, fabsf(y)));
        float e = bLen(x, y * 6.0f);
        float ang = atan2f(y * 6.0f, x);
        float swirl = 0.6f + 0.4f * sinf(ang * 3.0f + e * 30.0f - t * 4.0f);
        float disc = bSm(0.3f, 0.2f, e) * bSm(0.02f, 0.07f, e) * swirl;
        float core = xGl(bLen(x, y), 1500.0f) * 2.0f;
        r += jet * 0.5f + disc * 1.0f + core; g += jet * 0.6f + disc * 0.55f + core; b += jet * 1.2f + disc * 0.2f + core;
        xAddStars(r, g, b, st * 0.5f);
        break;
    }
    case 19: {  // Solar eclipse
        float d = bLen(x, y), ang = atan2f(y, x);
        float streak = bFbm(cosf(ang) * 3.0f + 4.0f, sinf(ang) * 3.0f + 4.0f + t * 0.1f);
        float cor = d > 0.2f ? expf(-(d - 0.2f) * (3.0f + 9.0f * (1.0f - streak))) : 0.0f;
        r += cor; g += cor * 0.95f; b += cor;
        float ring = xGl(d - 0.205f, 4000.0f);
        r += ring; g += ring; b += ring;
        float ba = 0.8f + t * 0.1f;
        float dm = bLen(x - 0.205f * cosf(ba), y - 0.205f * sinf(ba));
        float dia = xGl(dm, 2500.0f) * 1.6f + xGl(dm, 200.0f) * 0.3f;
        r += dia; g += dia; b += dia;
        xAddStars(r, g, b, st * 0.5f * bSm(0.25f, 0.5f, d));
        break;
    }
    case 20: {  // Cosmic web
        float wx = u * 4.5f + 0.12f * sinf(v * 7.0f + t * 0.6f), wy = v * 4.5f + 0.12f * sinf(u * 6.0f - t * 0.5f);
        float d1, d2, vid;
        xVor(wx, wy, d1, d2, vid);
        float fil = xGl(d2 - d1, 70.0f);
        float node = xGl(d1, 30.0f);
        float pulse = 0.55f + 0.45f * sinf(t * 2.0f + vid * 6.28f);
        xHue(r, g, b, 0.72f + vid * 0.15f, fil * 0.8f * pulse);
        r += node * 0.35f; g += node * 0.3f; b += node * 0.6f;
        xAddStars(r, g, b, st * 0.7f);
        break;
    }
    case 21: {  // City lights from orbit
        float n = bFbm(u * 4.0f + t * 0.02f, v * 4.0f + 2.0f);
        float uu = u * 46.0f, vv = v * 46.0f;
        int ci = (int)floorf(uu), cj = (int)floorf(vv);
        float h = Hh(ci, cj, 12);
        float dx = uu - ci - 0.5f, dy = vv - cj - 0.5f;
        float dens = bSm(0.52f, 0.75f, n);
        float lit = (h < dens) ? expf(-(dx * dx + dy * dy) * 14.0f) * (0.6f + 0.4f * sinf(t * 2.0f + h * 90.0f)) : 0.0f;
        r = 0.01f; g = 0.02f; b = 0.05f + n * 0.05f;
        float land = bSm(0.5f, 0.56f, n) * 0.025f;
        r += land; g += land; b += land * 0.6f;
        r += lit; g += lit * 0.75f; b += lit * 0.35f;
        float at = xGl(v, 12.0f) * 0.25f;
        g += at * 0.5f; b += at;
        float cl = bSm(0.6f, 0.9f, bFbm(u * 3.0f - t * 0.05f, v * 3.0f)) * 0.08f;
        r += cl; g += cl; b += cl;
        break;
    }
    case 22: {  // Binary stars
        xAddStars(r, g, b, st * 0.7f);
        float a = t * 1.1f;
        float p1x = cosf(a) * 0.17f, p1y = sinf(a) * 0.1f, p2x = -p1x, p2y = -p1y;
        float d1 = bLen(x - p1x, y - p1y), d2 = bLen(x - p2x, y - p2y);
        float s1 = xGl(d1, 1400.0f) * 2.0f + xGl(d1, 60.0f) * 0.5f;
        float s2 = xGl(d2, 2200.0f) * 2.0f + xGl(d2, 90.0f) * 0.5f;
        r += s1; g += s1 * 0.55f; b += s1 * 0.2f;
        r += s2 * 0.4f; g += s2 * 0.6f; b += s2;
        float br = xGl(bCap(x, y, p1x, p1y, p2x, p2y, 0.0f), 600.0f) * (0.3f + 0.7f * bFbm(x * 10.0f + t * 2.0f, y * 10.0f)) * 0.5f;
        r += br * 0.8f; g += br * 0.5f; b += br * 0.9f;
        break;
    }
    case 23: {  // Cosmic waves
        float f = 0.5f + 0.5f * sinf(u * 5.0f + sinf(v * 4.0f + t * 0.5f) * 2.0f + t * 0.3f);
        float f2 = 0.5f + 0.5f * sinf(v * 7.0f + sinf(u * 5.0f - t * 0.4f) * 2.0f);
        xHue(r, g, b, 0.55f + 0.3f * f + t * 0.02f, 0.25f + 0.5f * f2 * f2);
        float cn = xGl(f - 0.5f, 220.0f) * 0.35f;
        r += cn; g += cn; b += cn;
        xAddStars(r, g, b, st);
        break;
    }
    case 24: {  // UFO tractor beams
        xAddStars(r, g, b, st * 0.8f);
        float ux = 0.5f + 0.28f * sinf(t * 0.7f), uy = 0.22f;
        float dx = u - ux;
        float bw = 0.04f + 0.3f * (v - 0.27f);
        if (v > 0.27f && fabsf(dx) < bw) {
            float in = (0.35f + 0.25f * sinf(v * 40.0f - t * 6.0f)) * (1.0f - fabsf(dx) / bw) * (1.0f - 0.4f * (v - 0.27f));
            g += in * 0.9f; r += in * 0.35f; b += in * 0.4f;
        }
        float sd = bEll(u, v, ux, uy, 0.11f, 0.028f);
        bPut(r, g, b, 0.55f, 0.6f, 0.68f, bEdge(sd));
        float dm = bEll(u, v, ux, uy - 0.016f, 0.05f, 0.04f);
        if (v < uy - 0.005f) bPut(r, g, b, 0.45f, 0.85f, 0.8f, bEdge(dm) * 0.8f);
        for (int i = 0; i < 5; i++) {
            float lx = ux + (i - 2) * 0.04f;
            float pl = 0.5f + 0.5f * sinf(t * 6.0f + i * 1.3f);
            float gl = xGl(bLen(u - lx, v - uy - 0.008f), 20000.0f) * (0.5f + pl);
            r += gl; g += gl * 0.9f; b += gl * 0.4f;
        }
        float hill = 0.9f - 0.06f * sinf(u * 5.0f + 1.0f) - 0.04f * sinf(u * 11.0f);
        if (v > hill) { r *= 0.08f; g *= 0.08f; b *= 0.1f; }
        break;
    }
    case 25: {  // Stardust spiral
        float d = bLen(x, y) + 1e-4f, ang = atan2f(y, x);
        float q = Fr(ang / kTau * 3.0f + logf(d + 0.03f) * 1.1f - t * 0.04f);
        float arm = xGl(q - 0.5f, 9.0f) * expf(-d * 3.5f);
        float dust = bFbm(x * 10.0f, y * 10.0f);
        float core = xGl(d, 120.0f) * 1.4f;
        r += arm * (0.55f + 0.3f * dust) + core + arm * arm * 0.6f * dust; g += arm * 0.5f + core * 0.9f; b += arm * 0.9f + core * 0.7f;
        float sp = xStar(u, v, 40.0f, 21, t) * (0.2f + arm * 3.0f);
        xAddStars(r, g, b, sp + st * 0.4f);
        break;
    }
    case 26: {  // Big bang
        xAddStars(r, g, b, st * 0.4f);
        float d = bLen(x, y), ang = atan2f(y, x);
        for (int k = 0; k < 3; k++) {
            float T = Fr(t * 0.22f + k * 0.333f);
            float rr = T * 0.75f;
            float ring = xGl(d - rr, 1200.0f) * (1.0f - T);
            float sparks = 0.5f + 0.5f * sinf(ang * 24.0f + k * 2.0f + T * 4.0f);
            sparks *= sparks;
            xHue(r, g, b, 0.08f + k * 0.28f + T * 0.2f, ring * (0.35f + 0.9f * sparks));
        }
        float cr = xGl(d, 400.0f) * (0.8f + 0.2f * sinf(t * 8.0f));
        r += cr; g += cr; b += cr * 0.9f;
        break;
    }
    default: {  // 27 Rainbow nebula
        float h = bFbm(u * 2.5f + t * 0.04f, v * 2.5f) * 1.3f + t * 0.03f;
        float dn = bFbm(u * 4.0f, v * 4.0f - t * 0.05f);
        xHue(r, g, b, h, dn * dn * 2.2f);
        float d2 = bFbm(u * 6.0f + 9.0f, v * 6.0f - t * 0.03f);
        xHue(r, g, b, h + 0.5f, d2 * d2 * 0.8f);
        xAddStars(r, g, b, st);
        break;
    }
    }
}

// ---------------------------------------- WATER (29) ----------------------------------------
static void XWater(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.0f;
    float x = u - 0.5f, y = v - 0.5f;
    switch (id) {
    case 0: {   // Deep sea
        g = bMix(0.12f, 0.03f, v); b = bMix(0.4f, 0.14f, v);
        float c = xGl(bFbm(u * 5.0f + t * 0.12f, v * 5.0f - t * 0.1f) - 0.5f, 70.0f) * (1.0f - v) * 0.5f;
        r += c * 0.2f; g += c * 0.8f; b += c;
        float s = xDots(u, v, 24.0f, t * 0.35f, 0.4f * sinf(t * 0.5f + v * 5.0f), 0.2f, 50.0f) * 0.5f;
        r += s * 0.6f; g += s * 0.8f; b += s * 0.9f;
        break;
    }
    case 1: {   // Underwater rays
        float sk = u + v * 0.3f;
        float ray = bSm(0.35f, 0.9f, bFbm(sk * 12.0f + t * 0.15f, 3.0f + t * 0.05f)) * bSm(1.0f, 0.0f, v);
        float ray2 = bSm(0.4f, 0.9f, bFbm(sk * 25.0f - t * 0.2f, 8.0f)) * 0.5f * bSm(1.0f, 0.1f, v);
        float k = ray + ray2;
        r = k * 0.3f; g = 0.12f + k * 0.6f - v * 0.07f; b = 0.32f - v * 0.12f + k * 0.5f;
        break;
    }
    case 2: {   // Rain on pond
        float uu = u * 4.0f, vv = v * 4.0f;
        int ci = (int)floorf(uu), cj = (int)floorf(vv);
        float rip = 0.0f;
        for (int j = -1; j <= 1; j++) for (int i = -1; i <= 1; i++) {
            int gi = ci + i, gj = cj + j;
            float k = t * (0.4f + 0.3f * Hh(gi, gj, 61)) + Hh(gi, gj, 62);
            int cyc = (int)floorf(k);
            float ph = k - cyc;
            float px = gi + 0.2f + 0.6f * Hh(gi, gj, cyc + 63), py = gj + 0.2f + 0.6f * Hh(gi, gj, cyc + 64);
            float d = bLen(uu - px, vv - py);
            float rr = ph * 1.1f;
            rip += xGl(d - rr, 120.0f) * (1.0f - ph) * (0.5f + 0.5f * cosf((d - rr) * 40.0f));
        }
        r = 0.02f + rip * 0.5f; g = 0.25f + rip * 0.6f; b = 0.38f + rip * 0.55f;
        break;
    }
    case 3: {   // Whirlpool
        float d = bLen(x, y) + 1e-4f, ang = atan2f(y, x);
        float q = Fr(ang / kTau * 3.0f + logf(d + 0.05f) * 1.6f - t * 0.5f);
        float foam = xGl(q - 0.5f, 14.0f) * bSm(0.5f, 0.1f, d);
        float dark = bSm(0.02f, 0.3f, d);
        r = 0.02f + foam * 0.6f;
        g = (0.2f + 0.45f * (1.0f - d)) * (0.25f + 0.75f * dark) + foam * 0.6f;
        b = (0.42f + 0.2f * (1.0f - d)) * (0.3f + 0.7f * dark) + foam * 0.7f;
        break;
    }
    case 4: {   // Rolling wave
        float ys = 0.5f + 0.1f * sinf(u * 6.28f - t * 1.4f) + 0.05f * sinf(u * 18.0f - t * 2.6f) + 0.02f * sinf(u * 40.0f - t * 5.0f);
        float dd = v - ys;
        if (dd > 0.0f) {
            float dp = Cl(dd * 2.2f);
            r = (1.0f - dp) * 0.15f; g = bMix(0.55f, 0.15f, dp); b = bMix(0.75f, 0.35f, dp);
            float cr = xGl(bFbm(u * 6.0f - t * 0.3f, v * 6.0f) - 0.5f, 60.0f) * 0.25f * (1.0f - dp);
            g += cr; b += cr;
        } else {
            r = 0.55f + 0.3f * v; g = 0.75f + 0.2f * v; b = 0.95f;
        }
        float foam = xGl(dd, 1500.0f) * (0.6f + 0.4f * bFbm(u * 30.0f + t, v * 30.0f));
        r += foam; g += foam; b += foam;
        break;
    }
    case 5: {   // Rising bubbles
        g = bMix(0.08f, 0.3f, v); b = bMix(0.25f, 0.6f, v);
        float s = 0.0f;
        for (int L = 0; L < 3; L++) {
            float n = 6.0f + L * 5.0f;
            float sw = 0.3f * sinf(t * (0.5f + 0.2f * L) + v * 5.0f + L);
            float big = xDots(u, v, n, t * (0.5f + 0.35f * L), sw, 0.34f, 70.0f + L * 9.0f);
            float inn = xDots(u, v, n, t * (0.5f + 0.35f * L), sw, 0.26f, 70.0f + L * 9.0f);
            s += (big - inn * 0.85f) * (0.8f - 0.2f * L) + inn * 0.06f;
        }
        r += s * 0.7f; g += s * 0.9f; b += s;
        break;
    }
    case 6: {   // Coral reef
        g = bMix(0.35f, 0.15f, v); b = bMix(0.55f, 0.3f, v);
        for (int L = 0; L < 2; L++) for (int i = 0; i < 7; i++) {
            float cx = (i + 0.5f + 0.5f * L) / 7.5f + 0.01f * (Hh(i, 2 + L) - 0.5f);
            float h = (0.3f + 0.35f * Hh(i, 3 + L)) * (L == 0 ? 0.8f : 1.0f);
            float bx = cx + 0.03f * sinf(t * 0.9f + i * 1.7f + L * 2.0f);
            float dd = bTap(u, v, cx, 1.02f, bx, 1.0f - h, 0.035f, 0.012f);
            float a = bSm(0.004f, -0.004f, dd);
            float hr, hg, hb;
            Hsv(0.9f + Hh(i, 4 + L) * 0.2f, 0.7f, 1.0f, hr, hg, hb);
            float shade = (0.55f + 0.45f * (1.0f - v)) * (L == 0 ? 0.6f : 1.0f);
            bPut(r, g, b, hr * shade, hg * shade, hb * shade, a);
            float tp = xGl(bLen(u - bx, v - (1.0f - h)), 3000.0f) * 0.8f;
            r += hr * tp; g += hg * tp; b += hb * tp;
        }
        break;
    }
    case 7: {   // Shore foam
        float q = Fr(v * 1.6f + 0.03f * sinf(u * 11.0f + t) + 0.02f * sinf(u * 27.0f - t * 1.7f) - t * 0.2f);
        float sh = 0.85f + 0.15f * bFbm(u * 30.0f, v * 30.0f);
        float sr = 0.8f * sh, sg = 0.72f * sh, sb = 0.52f * sh;
        float wr = bMix(0.05f, 0.0f, q), wg = bMix(0.6f, 0.3f, q), wb = bMix(0.65f, 0.55f, q);
        float w = bSm(0.02f, 0.1f, q);
        r = bMix(sr, wr, w); g = bMix(sg, wg, w); b = bMix(sb, wb, w);
        float foam = bSm(0.0f, 0.03f, q) * bSm(0.2f, 0.05f, q) * (0.5f + 0.5f * bFbm(u * 25.0f - t, v * 25.0f));
        r = bMix(r, 0.97f, foam); g = bMix(g, 0.99f, foam); b = bMix(b, 1.0f, foam);
        break;
    }
    case 8: {   // Raindrops on glass
        float bg = 0.06f + 0.14f * bFbm(u * 3.0f, v * 3.0f);
        r = bg * 0.6f; g = bg * 0.8f; b = bg + 0.1f;
        for (int L = 0; L < 2; L++) {
            float n = 5.0f + 3.0f * L;
            float bk = xDots(u, v, n, 0.0f, 0.0f, 0.4f, 100.0f + L * 7.0f);
            float hue = Hh((int)floorf(u * n), (int)floorf(v * n), 109 + L);
            float hr, hg, hb;
            Hsv(hue, 0.6f, 1.0f, hr, hg, hb);
            float k = bk * 0.35f * (0.7f + 0.3f * sinf(t * 1.5f + hue * 30.0f));
            r += hr * k; g += hg * k; b += hb * k;
        }
        float uu = u * 8.0f, vv = v * 8.0f;
        int ci = (int)floorf(uu), cj = (int)floorf(vv);
        if (Hh(ci, cj, 112) > 0.45f) {
            float ox = 0.5f + 0.2f * (Hh(ci, cj, 111) - 0.5f), oy = 0.3f + 0.4f * Hh(ci, cj, 113) + 0.02f * sinf(t + Hh(ci, cj, 114) * 9.0f);
            float dx = uu - ci - ox, dy = vv - cj - oy;
            float dd = bLen(dx, dy * 0.8f);
            float ad = bSm(0.17f, 0.13f, dd);
            float hl = xGl(bLen(dx + 0.05f, dy + 0.06f), 400.0f);
            float tr = dy < 0.0f ? xGl(dx, 900.0f) * bSm(0.0f, -0.4f, dy) * 0.12f : 0.0f;
            r = bMix(r, r * 1.5f + 0.08f, ad) + hl * 0.5f * ad + tr;
            g = bMix(g, g * 1.5f + 0.1f, ad) + hl * 0.5f * ad + tr;
            b = bMix(b, b * 1.4f + 0.12f, ad) + hl * 0.55f * ad + tr;
        }
        break;
    }
    case 9: {   // Lagoon caustics
        float f1 = sinf(u * 14.0f + sinf(v * 9.0f + t) * 2.0f) + sinf(v * 13.0f + sinf(u * 8.0f - t * 0.8f) * 2.0f);
        float f2 = sinf((u + v) * 10.0f + sinf((u - v) * 7.0f + t * 0.7f) * 2.0f);
        float c = Cl(0.5f + 0.25f * (f1 + f2));
        c = c * c * c;
        r = c * 0.6f; g = 0.5f + c * 0.5f; b = 0.55f + c * 0.35f;
        break;
    }
    case 10: {  // Fountain
        g = 0.1f + 0.1f * v; b = 0.22f + 0.25f * v; r = 0.02f;
        float s = 0.0f;
        for (int k = 0; k < 9; k++) {
            float vx = (k - 4) * 0.05f, vy = 0.62f + 0.1f * Hh(k, 8);
            for (int j = 0; j < 7; j++) {
                float tau = Fr(t * 0.55f + j / 7.0f + k * 0.11f);
                float px = 0.5f + vx * tau * 2.0f;
                float py = 0.97f - vy * 0.8f * 4.0f * tau * (1.0f - tau);
                float dx = u - px, dy = v - py;
                s += expf(-(dx * dx + dy * dy) * 9000.0f) * (0.5f + 0.5f * (1.0f - tau));
            }
        }
        r += s * 0.6f; g += s * 0.9f; b += s;
        break;
    }
    case 11: {  // River flow
        float warp = 0.12f * sinf(u * 5.0f + t * 0.5f);
        float n = bFbm(u * 3.0f - t * 0.9f, (v + warp) * 22.0f);
        float n2 = bFbm(u * 5.0f - t * 1.6f + 9.0f, (v - warp) * 30.0f);
        float f = Cl(0.35f + 1.8f * n * n2);
        r = f * f * 0.5f; g = 0.2f + f * 0.6f; b = 0.4f + f * 0.55f;
        break;
    }
    case 12: {  // Sun glitter sea
        g = bMix(0.1f, 0.25f, v); b = bMix(0.3f, 0.5f, v);
        float s = bVn(u * 40.0f + t * 1.1f, v * 30.0f - t * 0.7f);
        float tw = Cl((s - 0.78f) * 6.0f) * (0.5f + 0.5f * sinf(t * 5.0f + u * 30.0f + v * 20.0f));
        float path = xGl(u - 0.5f, 5.0f) * (0.3f + 0.7f * v);
        tw *= 0.15f + 1.6f * path;
        r += tw + path * 0.08f; g += tw + path * 0.08f; b += tw * 0.9f + path * 0.05f;
        break;
    }
    case 13: {  // Moonlit sea
        const float hor = 0.35f;
        float dm = bLen(u - 0.5f, v - 0.17f);
        if (v < hor) {
            r = 0.02f; g = 0.04f + 0.04f * v; b = 0.1f + 0.2f * v;
            float moon = bSm(0.075f, 0.065f, dm), mg = xGl(dm, 40.0f) * 0.3f;
            r += moon * 0.95f + mg * 0.8f; g += moon * 0.95f + mg * 0.85f; b += moon * 0.85f + mg;
            float s = xStar(u, v, 16.0f, 3, t) * 0.6f;
            xAddStars(r, g, b, s);
        } else {
            float dp = v - hor;
            g = 0.03f + 0.03f * dp; b = 0.1f + 0.05f * dp;
            float wob = 0.05f * sinf(v * 40.0f - t * 1.6f) * (0.3f + dp);
            float refl = xGl(u - 0.5f + wob, 120.0f / (1.0f + dp * 4.0f)) * Cl(0.4f + 0.8f * sinf(v * 80.0f - t * 2.0f)) * (1.0f - 0.5f * dp);
            r += refl * 0.8f; g += refl * 0.85f; b += refl * 0.7f;
            float hl = xGl(dp, 3000.0f) * 0.15f;
            r += hl; g += hl; b += hl;
        }
        break;
    }
    case 14: {  // Drop impact
        r = 0.02f; g = 0.18f + 0.1f * v; b = 0.3f + 0.15f * v;
        float d = bLen(x, y * 1.4f);
        float T = Fr(t * 0.35f);
        float ring = 0.0f;
        for (int k = 0; k < 3; k++) {
            float rr = T * 0.55f - k * 0.08f;
            if (rr > 0.0f) ring += xGl(d - rr, 1400.0f) * (1.0f - T) * (1.0f - 0.25f * k);
        }
        float dr = 0.0f;
        for (int k = 0; k < 12; k++) {
            float a = k * kTau / 12.0f + 0.2f;
            float rad = 0.04f + T * 0.3f;
            float hh = 0.22f * sinf(T * kPiX) * (0.6f + 0.4f * Hh(k, 17));
            float px = cosf(a) * rad, py = sinf(a) * rad * 0.7f - hh;
            dr += xGl(bLen(x - px, y - py), 6000.0f);
        }
        r += ring * 0.6f + dr * 0.8f; g += ring * 0.8f + dr * 0.95f; b += ring + dr;
        break;
    }
    case 15: {  // Kelp forest
        g = bMix(0.35f, 0.12f, v); b = bMix(0.45f, 0.2f, v);
        float ry = bSm(0.4f, 0.9f, bFbm((u + v * 0.3f) * 10.0f + t * 0.1f, 2.0f)) * (1.0f - v) * 0.25f;
        g += ry; b += ry;
        for (int L = 0; L < 2; L++) for (int i = 0; i < 6; i++) {
            float base = (i + 0.5f + 0.5f * L) / 6.5f + 0.04f * (Hh(i, 9 + L) - 0.5f);
            float sway = (0.045f + 0.02f * L) * sinf(t * (0.9f + 0.3f * Hh(i, 10)) + v * 5.0f + i * 1.3f) * (1.0f - v);
            float w = (0.018f + 0.012f * Hh(i, 11 + L)) * (0.5f + 0.5f * v);
            float dx = fabsf(u - (base + sway));
            float top = 0.08f + 0.3f * Hh(i, 12 + L);
            float a = bSm(w, w * 0.5f, dx) * bSm(top, top + 0.04f, v);
            float shade = (L == 0 ? 0.55f : 1.0f) * (0.6f + 0.4f * (1.0f - v));
            bPut(r, g, b, 0.12f * shade, 0.55f * shade, 0.2f * shade, a);
        }
        break;
    }
    case 16: {  // Ink in water
        float wx = u * 3.0f + 1.5f * bFbm(u * 3.0f + t * 0.1f, v * 3.0f), wy = v * 3.0f + 1.5f * bFbm(u * 3.0f + 5.0f, v * 3.0f - t * 0.12f);
        float n = bFbm(wx, wy);
        float ink = bSm(0.42f, 0.7f, n);
        r = bMix(0.55f, 0.25f, ink); g = bMix(0.85f, 0.0f, ink); b = bMix(0.9f, 0.45f, ink);
        float edge = xGl(n - 0.55f, 200.0f) * 0.6f;
        r += edge * 0.7f; b += edge * 0.4f;
        break;
    }
    case 17: {  // Bioluminescence
        g = 0.015f + 0.02f * v; b = 0.06f + 0.06f * v;
        float s = 0.0f;
        s += xDots(u, v, 16.0f, t * 0.3f, 0.3f * sinf(t * 0.6f + v * 5.0f), 0.3f, 130.0f) * (0.5f + 0.5f * sinf(t * 3.0f + u * 25.0f));
        s += xDots(u, v, 9.0f, -t * 0.2f, 0.35f * sinf(t * 0.4f + v * 3.0f), 0.34f, 140.0f) * (0.5f + 0.5f * sinf(t * 2.0f + v * 20.0f));
        s += xDots(u, v, 28.0f, t * 0.45f, 0.2f * sinf(t + v * 9.0f), 0.28f, 150.0f) * 0.6f * (0.5f + 0.5f * sinf(t * 4.0f + u * 50.0f));
        float swell = xGl(bFbm(u * 3.0f + t * 0.15f, v * 3.0f - t * 0.1f) - 0.55f, 90.0f) * 0.35f;
        r += s * 0.1f; g += s * 0.9f + swell * 0.7f; b += s + swell;
        break;
    }
    case 18: {  // Foam lace
        float wx = u * 7.0f + 0.25f * sinf(v * 8.0f + t * 0.7f), wy = v * 7.0f + 0.25f * sinf(u * 7.0f - t * 0.6f);
        float d1, d2, vid;
        xVor(wx, wy, d1, d2, vid);
        float lace = bSm(0.16f, 0.0f, d2 - d1);
        r = 0.05f; g = 0.45f + 0.15f * vid; b = 0.55f + 0.1f * vid;
        float hl = xGl(d1, 25.0f) * 0.1f;
        r += hl; g += hl; b += hl;
        r = bMix(r, 0.95f, lace * 0.9f); g = bMix(g, 0.98f, lace * 0.9f); b = bMix(b, 1.0f, lace * 0.9f);
        break;
    }
    case 19: {  // Sand ripples
        float f = (u * 0.4f + v) * 26.0f + 4.0f * bFbm(u * 4.0f, v * 4.0f);
        float rip = 0.5f + 0.5f * sinf(f);
        float c1 = Cl(0.5f + 0.25f * (sinf(u * 14.0f + sinf(v * 9.0f + t) * 2.0f) + sinf(v * 13.0f + sinf(u * 8.0f - t * 0.8f) * 2.0f)));
        c1 = c1 * c1 * c1;
        float sd = 0.65f + 0.35f * rip;
        r = 0.75f * sd * 0.5f + c1 * 0.5f; g = 0.68f * sd * 0.95f + c1 * 0.6f; b = 0.45f * sd + 0.15f + c1 * 0.4f;
        break;
    }
    case 20: {  // Pool tiles
        float uu = u + 0.025f * sinf(v * 14.0f + t * 1.5f) + 0.012f * sinf(v * 31.0f - t * 2.3f);
        float vv = v + 0.025f * sinf(u * 12.0f - t * 1.3f) + 0.012f * sinf(u * 27.0f + t * 2.0f);
        float gr = Cl(xGl(xEdge(uu * 8.0f), 700.0f) + xGl(xEdge(vv * 8.0f), 700.0f));
        float ca = Cl(0.5f + 0.25f * (sinf(u * 14.0f + sinf(v * 9.0f + t) * 2.0f) + sinf(v * 13.0f + sinf(u * 8.0f - t * 0.8f) * 2.0f)));
        ca = ca * ca * ca;
        r = 0.12f + ca * 0.4f; g = 0.55f + ca * 0.45f; b = 0.8f + ca * 0.2f;
        r = bMix(r, 0.8f, gr * 0.7f); g = bMix(g, 0.9f, gr * 0.7f); b = bMix(b, 0.95f, gr * 0.7f);
        break;
    }
    case 21: {  // Hot spring
        float stm = bSm(0.42f, 0.85f, bFbm(u * 4.0f + 0.4f * sinf(v * 3.0f + t * 0.5f), v * 3.0f + t * 0.45f)) * bSm(0.95f, 0.2f, v);
        float wl = bSm(0.62f, 0.66f, v + 0.02f * sinf(u * 20.0f + t));
        float ca = Cl(0.5f + 0.25f * (sinf(u * 14.0f + sinf(v * 9.0f + t) * 2.0f) + sinf(v * 13.0f + sinf(u * 8.0f - t * 0.8f) * 2.0f)));
        ca = ca * ca * ca * 0.35f;
        r = bMix(0.12f, 0.05f + ca * 0.4f, wl); g = bMix(0.15f, 0.5f + ca, wl); b = bMix(0.22f, 0.55f + ca * 0.6f, wl);
        r += stm * 0.7f; g += stm * 0.7f; b += stm * 0.72f;
        break;
    }
    case 22: {  // Stormy sea
        float cl = bFbm(u * 3.0f + t * 0.05f, v * 6.0f);
        r = 0.12f + 0.2f * cl; g = 0.16f + 0.22f * cl; b = 0.2f + 0.25f * cl;
        float fl = Hh((int)floorf(t * 3.0f), 9) > 0.93f ? 0.35f : 0.0f;
        r += fl; g += fl; b += fl;
        for (int L = 0; L < 4; L++) {
            float ys = 0.38f + L * 0.17f + (0.045f + 0.02f * L) * sinf(u * (5.0f + 2.0f * L) + t * (1.0f + 0.3f * L) + L * 2.0f) + 0.015f * sinf(u * 17.0f - t * 2.0f + L);
            float dd = v - ys;
            float shade = 0.35f + 0.18f * L;
            if (dd > 0.0f) { r = 0.02f + 0.06f * shade; g = 0.1f + 0.22f * shade; b = 0.14f + 0.25f * shade; }
            float foam = xGl(dd, 2500.0f) * (0.4f + 0.6f * bFbm(u * 20.0f + t, L * 7.0f));
            r += foam * 0.8f; g += foam * 0.85f; b += foam * 0.9f;
        }
        break;
    }
    case 23: {  // Seigaiha waves
        float d, idc;
        xScaleCell(u, v, 6.0f, d, idc);
        float ln = xGl(xEdge(d * 6.0f - t * 0.2f), 250.0f);
        float sh = 0.8f + 0.4f * idc;
        r = 0.05f * sh; g = 0.22f * sh; b = 0.5f * sh;
        r += ln * 0.85f * 0.9f; g += ln * 0.95f * 0.9f; b += ln * 1.0f * 0.9f;
        break;
    }
    case 24: {  // Lily pond
        g = bMix(0.22f, 0.12f, v); b = bMix(0.26f, 0.16f, v); r = 0.02f;
        float c = xGl(bFbm(u * 5.0f + t * 0.1f, v * 5.0f) - 0.5f, 70.0f) * 0.12f;
        g += c; b += c * 1.2f;
        float uu = u * 3.0f + 0.08f * sinf(t * 0.4f + v * 3.0f), vv = v * 3.0f + 0.05f * sinf(t * 0.35f + u * 3.0f);
        int ci = (int)floorf(uu), cj = (int)floorf(vv);
        if (Hh(ci, cj, 160) > 0.3f) {
            float ox = 0.5f + 0.3f * (Hh(ci, cj, 161) - 0.5f), oy = 0.5f + 0.3f * (Hh(ci, cj, 162) - 0.5f);
            float dx = uu - ci - ox, dy = vv - cj - oy;
            float d = bLen(dx, dy);
            float R0 = 0.3f + 0.08f * Hh(ci, cj, 163);
            float a0 = Hh(ci, cj, 164) * 6.28f;
            float nx = cosf(a0), ny = sinf(a0);
            float al = dx * nx + dy * ny, pe = -dx * ny + dy * nx;
            bool notch = al > 0.0f && fabsf(pe) < al * 0.25f;
            if (!notch) {
                float lit = 0.7f + 0.3f * (1.0f - d / R0);
                bPut(r, g, b, 0.1f * lit, 0.45f * lit, 0.15f * lit, bSm(R0, R0 - 0.015f, d));
            }
            if (Hh(ci, cj, 165) > 0.7f) {
                float pet = 0.5f + 0.5f * cosf(atan2f(dy, dx) * 8.0f);
                float fr = 0.06f + 0.03f * pet;
                float hr, hg, hb;
                Hsv(0.92f, 0.45f, 1.0f, hr, hg, hb);
                bPut(r, g, b, hr, hg, hb, bSm(fr, fr * 0.8f, d));
            }
        }
        break;
    }
    case 25: {  // Fish school
        g = bMix(0.4f, 0.12f, v); b = bMix(0.6f, 0.3f, v);
        float ca = xGl(bFbm(u * 5.0f + t * 0.1f, v * 5.0f - t * 0.08f) - 0.5f, 60.0f) * 0.15f;
        g += ca; b += ca;
        for (int i = 0; i < 16; i++) {
            float ph = i * 0.9f;
            float cx = 0.5f + 0.32f * sinf(t * 0.55f + ph * 0.35f) + 0.07f * sinf(t * 1.7f + ph);
            float cy = 0.5f + 0.27f * sinf(t * 0.42f + ph * 0.3f + 1.0f) + 0.06f * cosf(t * 1.3f + ph * 1.4f);
            float vx = 0.32f * 0.55f * cosf(t * 0.55f + ph * 0.35f) + 0.07f * 1.7f * cosf(t * 1.7f + ph);
            float vy = 0.27f * 0.42f * cosf(t * 0.42f + ph * 0.3f + 1.0f) - 0.06f * 1.3f * sinf(t * 1.3f + ph * 1.4f);
            float vl = bLen(vx, vy) + 1e-4f;
            vx /= vl; vy /= vl;
            float dx = u - cx, dy = v - cy;
            float al = dx * vx + dy * vy, pe = -dx * vy + dy * vx;
            float body = bLen(al / 0.045f, pe / 0.02f) - 1.0f;
            float ab = bSm(0.2f, -0.2f, body);
            float tl = (al < -0.035f && al > -0.075f && fabsf(pe) < (-al - 0.035f) * 0.9f) ? 1.0f : 0.0f;
            float lum = 0.6f + 0.4f * Cl(0.5f - pe / 0.02f * 0.5f);
            bool orange = Hh(i, 3) > 0.7f;
            float cr = orange ? 1.0f : 0.75f, cg = orange ? 0.55f : 0.85f, cb = orange ? 0.15f : 0.95f;
            bPut(r, g, b, cr * lum, cg * lum, cb * lum, Cl(ab + tl));
        }
        break;
    }
    case 26: {  // Sonar pings
        g = 0.07f; b = 0.12f;
        float d = bLen(x, y);
        float gr = xGl(xEdge(x * 10.0f), 1200.0f) + xGl(xEdge(y * 10.0f), 1200.0f);
        g += gr * 0.06f; b += gr * 0.08f;
        for (int k = 0; k < 3; k++) {
            float T = Fr(t * 0.3f + k * 0.34f);
            float ring = xGl(d - T * 0.75f, 900.0f) * (1.0f - T);
            g += ring * 0.8f; b += ring * 0.9f; r += ring * 0.15f;
        }
        for (int k = 0; k < 6; k++) {
            float bx = (Hh(k, 20) - 0.5f) * 0.8f, by = (Hh(k, 21) - 0.5f) * 0.8f;
            float bd = bLen(bx, by);
            float rt = Fr((t * 0.3f - bd / 0.75f) * 2.94f);
            float gl = xGl(bLen(x - bx, y - by), 3000.0f) * expf(-rt * 3.5f);
            r += gl * 0.3f; g += gl; b += gl * 0.8f;
        }
        break;
    }
    case 27: {  // Oil slick
        float h = bFbm(u * 3.0f + t * 0.08f, v * 3.0f - t * 0.06f) * 5.0f + t * 0.15f;
        float lum = 0.35f + 0.65f * bFbm(u * 2.0f + 8.0f, v * 2.0f - t * 0.05f);
        r = (0.5f + 0.5f * cosf(kTau * h)) * lum * 0.85f + 0.02f;
        g = (0.5f + 0.5f * cosf(kTau * (h + 0.33f))) * lum * 0.85f + 0.02f;
        b = (0.5f + 0.5f * cosf(kTau * (h + 0.67f))) * lum * 0.85f + 0.02f;
        break;
    }
    default: {  // 28 Rapids
        float f = bFbm(u * 6.0f, v * 8.0f + t * 2.2f) * 0.6f + bFbm(u * 12.0f + 3.0f, v * 14.0f + t * 3.5f) * 0.4f;
        float foam = bSm(0.5f, 0.75f, f);
        r = bMix(0.05f, 0.9f, foam); g = bMix(0.35f, 0.97f, foam); b = bMix(0.6f, 1.0f, foam);
        float d1, d2, vid;
        xVor(u * 3.5f + 0.1f * sinf(v * 6.0f) + 4.0f, v * 3.5f + 4.0f, d1, d2, vid);
        if (vid > 0.55f) {
            float rk = bSm(0.2f, 0.15f, d1);
            float halo = xGl(d1 - 0.2f, 200.0f) * (0.6f + 0.4f * sinf(t * 6.0f + v * 30.0f));
            r += halo; g += halo; b += halo;
            bPut(r, g, b, 0.18f + 0.1f * vid, 0.17f + 0.08f * vid, 0.16f, rk);
        }
        break;
    }
    }
}

// ---------------------------------------- GOLD (29) ----------------------------------------
static void XGold(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = 0.04f; g = 0.025f; b = 0.0f;
    float x = u - 0.5f, y = v - 0.5f;
    switch (id) {
    case 0: {   // Liquid gold
        float wx = u * 3.0f + 1.2f * bFbm(u * 3.0f + t * 0.1f, v * 3.0f), wy = v * 3.0f + 1.2f * bFbm(u * 3.0f + 4.0f, v * 3.0f - t * 0.12f);
        float f = 0.5f + 0.5f * sinf(bFbm(wx, wy) * 14.0f + t * 0.6f);
        xGoldRamp(0.15f + 0.85f * f, r, g, b);
        break;
    }
    case 1: {   // Gold foil
        float d1, d2, vid;
        xVor(u * 5.0f, v * 5.0f, d1, d2, vid);
        float sh = 0.3f + 0.5f * vid + 0.25f * sinf(t * 1.1f + vid * 25.0f) * (0.5f + 0.5f * vid);
        float edge = bSm(0.10f, 0.0f, d2 - d1);
        xGoldRamp(sh * (1.0f - 0.7f * edge) + 0.15f * edge, r, g, b);
        break;
    }
    case 2: {   // Gold coins
        float uu = u * 4.0f, vv = v * 4.0f;
        int cj = (int)floorf(vv);
        float off = (cj & 1) ? 0.5f : 0.0f;
        float fx = Fr(uu + off) - 0.5f, fy = Fr(vv) - 0.5f;
        float d = bLen(fx, fy);
        float f = 0.55f;
        f += 0.3f * xGl(d - 0.42f, 900.0f);
        f -= 0.3f * xGl(d - 0.3f, 2000.0f);
        f += d < 0.18f ? 0.12f : 0.0f;
        f += 0.25f * (-fx * 0.7f - fy * 0.7f);
        f += 0.5f * xGl(Fr((u + v) * 0.5f - t * 0.25f) - 0.5f, 40.0f);
        float cr, cg, cb;
        xGoldRamp(f, cr, cg, cb);
        float a = bSm(0.46f, 0.44f, d);
        r = bMix(0.06f, cr, a); g = bMix(0.035f, cg, a); b = bMix(0.0f, cb, a);
        break;
    }
    case 3: {   // Gold dust
        xGoldRamp(0.1f + bFbm(u * 4.0f, v * 4.0f) * 0.15f, r, g, b);
        r *= 0.6f; g *= 0.6f; b *= 0.6f;
        float s = xStar(u, v, 40.0f, 31, t) * 1.2f + xStar(u, v, 18.0f, 37, t * 0.8f) * 1.6f + xStar(u, v, 70.0f, 41, t * 1.4f) * 0.8f;
        r += s; g += s * 0.78f; b += s * 0.3f;
        break;
    }
    case 4: {   // Brushed gold
        float line = Hh((int)floorf(v * 260.0f), 5);
        float sweep = xGl(Fr(u * 0.8f + v * 0.15f - t * 0.12f) - 0.5f, 25.0f);
        float f = 0.38f + 0.22f * line + 0.5f * sweep * (0.6f + 0.4f * line) + 0.08f * sinf(u * 5.0f + t * 0.4f);
        xGoldRamp(f, r, g, b);
        break;
    }
    case 5: {   // Gold hexagons
        float px = u * 6.0f, py = v * 6.0f;
        float ax = nMod(px, 1.0f) - 0.5f, ay = nMod(py, 1.732f) - 0.866f;
        float bx = nMod(px - 0.5f, 1.0f) - 0.5f, by = nMod(py - 0.866f, 1.732f) - 0.866f;
        bool useA = ax * ax + ay * ay < bx * bx + by * by;
        float gx = useA ? ax : bx, gy = useA ? ay : by;
        float hd = bMax(fabsf(gx) * 0.5f + fabsf(gy) * 0.866f, fabsf(gx));
        int id2 = useA ? ((int)floorf(px) + 31 * (int)floorf(py / 1.732f)) : (1000 + (int)floorf(px - 0.5f) + 31 * (int)floorf((py - 0.866f) / 1.732f));
        float h = Hh(id2, 4);
        float edge = bSm(0.42f, 0.5f, hd);
        float pulse = 0.5f + 0.5f * sinf(t * 1.6f + h * 6.28f);
        float f = (0.35f + 0.45f * h + 0.2f * pulse) * (1.0f - 0.8f * edge) + 0.3f * (1.0f - bSm(0.0f, 0.3f, hd)) * 0.3f;
        xGoldRamp(f, r, g, b);
        break;
    }
    case 6: {   // Art deco fans
        float d, idc;
        xScaleCell(u, v, 4.0f, d, idc);
        float ln = xGl(xEdge(d * 5.0f), 110.0f);
        float f = 0.1f + 0.75f * ln + 0.3f * xGl(Fr(v * 0.7f - t * 0.2f) - 0.5f, 30.0f) * ln + 0.04f * idc;
        f += 0.35f * xGl(d - 0.5f, 120.0f);
        xGoldRamp(f, r, g, b);
        break;
    }
    case 7: {   // Gold glitter
        float uu = u * 30.0f, vv = v * 30.0f;
        int ci = (int)floorf(uu), cj = (int)floorf(vv);
        float h = Hh(ci, cj, 6);
        float tw = Cl(0.5f + 0.5f * sinf(t * (1.5f + 3.0f * h) + h * 60.0f));
        tw = tw * tw * tw;
        float edge = bSm(0.0f, 0.1f, Fr(uu)) * bSm(1.0f, 0.9f, Fr(uu)) * bSm(0.0f, 0.1f, Fr(vv)) * bSm(1.0f, 0.9f, Fr(vv));
        float f = (0.22f + 0.15f * h + 0.9f * tw * (0.3f + 0.7f * h)) * (0.7f + 0.3f * edge);
        xGoldRamp(f, r, g, b);
        break;
    }
    case 8: {   // Gold bars
        float uu = u * 3.0f, vv = v * 6.0f;
        int rw = (int)floorf(vv);
        float off = (rw & 1) ? 0.5f : 0.0f;
        float fx = Fr(uu + off), fy = Fr(vv);
        float ex = bMin(fx, 1.0f - fx) * 2.0f, ey = bMin(fy, 1.0f - fy);
        float e = bMin(ex, ey);
        float f;
        if (e < 0.04f) f = 0.02f;
        else {
            f = 0.62f + 0.1f * Hh((int)floorf(uu + off), rw, 3);
            if (e < 0.2f) {
                float k = 1.0f - (e - 0.04f) / 0.16f;
                bool topLeft = (ey < ex) ? (fy < 0.5f) : (fx < 0.5f);
                f += topLeft ? 0.3f * k : -0.28f * k;
            }
            f += 0.4f * xGl(Fr((u + v) * 0.6f - t * 0.2f) - 0.5f, 50.0f);
        }
        xGoldRamp(f, r, g, b);
        break;
    }
    case 9: {   // Royal gold & purple
        float s = Fr((u + v) * 3.0f - t * 0.1f);
        float band = bSm(0.0f, 0.03f, s) * bSm(0.5f, 0.47f, s);
        float gr, gg, gb;
        xGoldRamp(0.45f + 0.5f * sinf(s / 0.5f * kPiX), gr, gg, gb);
        float pr = 0.28f + 0.12f * sinf(s * 6.0f + t), pb = 0.42f + 0.15f * sinf(s * 6.0f + t + 1.0f);
        r = bMix(pr, gr, band); g = bMix(0.02f, gg, band); b = bMix(pb, gb, band);
        float sp = xStar(u, v, 30.0f, 51, t);
        r += sp; g += sp * 0.85f; b += sp * 0.6f;
        break;
    }
    case 10: {  // Gold & red
        float uu = u * 5.0f, vv = v * 5.0f;
        float d = bLen(Fr(uu) - 0.5f, Fr(vv) - 0.5f);
        float d2 = bLen(Fr(uu + 0.5f) - 0.5f, Fr(vv + 0.5f) - 0.5f);
        float a = Cl(xGl(xEdge(d * 6.0f), 500.0f) + 0.8f * xGl(xEdge(d2 * 6.0f), 500.0f));
        float sweep = xGl(Fr((u + v) * 0.7f - t * 0.2f) - 0.5f, 30.0f);
        float gr, gg, gb;
        xGoldRamp(0.55f + 0.45f * sweep, gr, gg, gb);
        float rr = 0.5f + 0.1f * sinf(t + u * 8.0f);
        r = bMix(rr, gr, a); g = bMix(0.03f, gg, a); b = bMix(0.04f, gb, a);
        break;
    }
    case 11: {  // Gold leaf
        float d1, d2, vid;
        xVor(u * 7.0f, v * 7.0f, d1, d2, vid);
        float patch = bSm(0.40f, 0.52f, bFbm(u * 5.0f + 2.0f, v * 5.0f));
        float cov = (vid > 0.22f ? 1.0f : 0.0f) * bSm(0.0f, 0.05f, d2 - d1) * patch;
        float gr, gg, gb;
        xGoldRamp(0.4f + 0.5f * vid + 0.15f * sinf(t * 1.3f + vid * 30.0f), gr, gg, gb);
        r = bMix(0.22f, gr, cov); g = bMix(0.06f, gg, cov); b = bMix(0.03f, gb, cov);
        break;
    }
    case 12: {  // Gold chain
        float uu = u * 6.0f, vv = v * 4.0f;
        float fy = Fr(vv) - 0.5f;
        int i0 = (int)floorf(uu);
        float al = 0.0f, f = 0.5f;
        for (int k = -1; k <= 1; k++) {
            int li = i0 + k;
            float fxk = uu - li - 0.5f;
            if ((li & 1) == 0) {
                float e = fabsf(bLen(fxk / 0.78f, fy / 0.34f) - 1.0f) * 0.3f;
                float a = bSm(0.09f, 0.06f, e);
                if (a > 0.0f) { al = a; f = 0.5f - 0.35f * Cl(fy / 0.34f) + 0.1f; }
            } else {
                float bd = xBox(fxk, fy, 0.4f, 0.1f);
                float a = bSm(0.02f, -0.01f, bd);
                if (a > 0.0f) { al = a; f = 0.55f + 0.3f * Cl(-fy / 0.1f); }
            }
        }
        f += 0.4f * xGl(Fr(u * 0.8f + v * 0.3f - t * 0.2f) - 0.5f, 40.0f);
        float cr, cg, cb;
        xGoldRamp(f, cr, cg, cb);
        r = bMix(0.03f, cr, al); g = bMix(0.02f, cg, al); b = bMix(0.0f, cb, al);
        break;
    }
    case 13: {  // Deco diamonds
        float a1 = u * 4.0f + v * 4.0f, a2 = u * 4.0f - v * 4.0f;
        float ln = Cl(xGl(xEdge(a1), 500.0f) + xGl(xEdge(a2), 500.0f));
        float dd = fabsf(Fr(a1) - 0.5f) + fabsf(Fr(a2) - 0.5f);
        float h = Hh((int)floorf(a1), (int)floorf(a2), 8);
        float f = 0.1f + 0.7f * ln + 0.5f * xGl(dd - 0.2f, 700.0f);
        if (h > 0.7f) f += 0.28f * (0.5f + 0.5f * sinf(t * 2.0f + h * 30.0f)) * bSm(0.15f, 0.0f, dd);
        f += 0.25f * xGl(Fr(u * 0.6f + v * 0.4f - t * 0.15f) - 0.5f, 40.0f);
        xGoldRamp(f, r, g, b);
        break;
    }
    case 14: {  // Gold rain
        float f = 0.0f;
        for (int L = 0; L < 2; L++) {
            float N = L == 0 ? 34.0f : 60.0f;
            int col = (int)floorf(u * N);
            float fx = u * N - col - 0.5f;
            float h = Hh(col, 12 + L), sp = 0.25f + 0.55f * Hh(col, 13 + L);
            float head = Fr(t * sp + h);
            float dd = Fr(head - v);
            float in = expf(-dd * 7.0f) * expf(-fx * fx * 30.0f) * (L == 0 ? 1.3f : 0.6f);
            f += in;
        }
        xGoldRamp(0.08f + f, r, g, b);
        break;
    }
    case 15: {  // Rose gold swirl
        float f = 0.5f + 0.2f * sinf(u * 7.0f + t * 0.6f) + 0.2f * sinf(v * 9.0f - t * 0.5f + u * 3.0f) + 0.15f * sinf((u + v) * 13.0f + t * 0.9f);
        f = Cl(f);
        r = Cl(0.14f + f); g = Cl(0.05f + f * f * 0.62f + f * 0.1f); b = Cl(0.05f + f * f * 0.58f);
        break;
    }
    case 16: {  // Gold circuit
        float uu = u * 9.0f, vv = v * 9.0f;
        int ci = (int)floorf(uu), cj = (int)floorf(vv);
        float fx = Fr(uu) - 0.5f, fy = Fr(vv) - 0.5f;
        bool hz = Hh(ci, cj, 14) > 0.4f, vt = Hh(ci, cj, 15) > 0.4f;
        float tr = 0.0f;
        if (hz) tr = bMax(tr, bSm(0.06f, 0.03f, fabsf(fy)));
        if (vt) tr = bMax(tr, bSm(0.06f, 0.03f, fabsf(fx)));
        float cd = bLen(fx, fy);
        if (hz || vt) tr = bMax(tr, bSm(0.14f, 0.1f, cd));
        float ph = 0.5f + 0.5f * sinf(t * 3.0f - (uu + vv) * 0.9f);
        float f = 0.12f + tr * (0.45f + 0.5f * ph * ph);
        if ((hz || vt) && cd < 0.05f) f = 0.1f;
        xGoldRamp(f, r, g, b);
        break;
    }
    case 17: {  // Gold spiral
        float d = bLen(x, y) + 1e-4f, ang = atan2f(y, x);
        float q = Fr(ang / kTau * 4.0f + d * 6.0f - t * 0.35f);
        float band = bSm(0.0f, 0.1f, q) * bSm(0.55f, 0.45f, q);
        float f = 0.12f + band * (0.4f + 0.6f * (1.0f - q * 1.8f)) + xGl(d, 200.0f) * 0.5f;
        xGoldRamp(f, r, g, b);
        break;
    }
    case 18: {  // Gold mandala
        float d = bLen(x, y), ang = atan2f(y, x) + t * 0.15f;
        float pet = 0.5f + 0.5f * cosf(ang * 12.0f);
        float f = 0.08f;
        f += xGl(d - (0.14f + 0.1f * pet), 1500.0f) * 0.9f;
        f += xGl(d - (0.26f + 0.08f * (1.0f - pet)), 1500.0f) * 0.7f;
        f += xGl(xEdge(d * 12.0f), 600.0f) * 0.25f * bSm(0.5f, 0.1f, d);
        f += xGl(d, 400.0f) * 0.9f;
        f += 0.3f * xGl(Fr(ang / kTau * 24.0f) - 0.5f, 80.0f) * bSm(0.45f, 0.2f, d) * bSm(0.1f, 0.15f, d);
        f *= 0.85f + 0.15f * sinf(t * 2.0f - d * 10.0f);
        xGoldRamp(f, r, g, b);
        break;
    }
    case 19: {  // Gold marble
        float n = bFbm(u * 3.0f + t * 0.02f, v * 3.0f);
        float vein = xGl(bFbm(u * 4.0f + n * 2.0f, v * 4.0f + t * 0.03f) - 0.5f, 220.0f);
        float vein2 = xGl(bFbm(u * 9.0f + 5.0f + n * 1.5f, v * 9.0f) - 0.5f, 500.0f) * 0.6f;
        float base = 0.86f + 0.1f * n;
        r = base * 0.97f; g = base * 0.93f; b = base * 0.84f;
        float gr, gg, gb;
        xGoldRamp(0.6f + 0.35f * sinf(n * 9.0f + t * 0.5f), gr, gg, gb);
        float a = Cl(vein + vein2);
        r = bMix(r, gr, a); g = bMix(g, gg, a); b = bMix(b, gb, a);
        break;
    }
    case 20: {  // Molten gold
        float n = bFbm(u * 3.0f - t * 0.2f, v * 4.0f + sinf(u * 4.0f + t * 0.4f) * 0.4f);
        float f = 0.12f + 1.25f * xGl(n - 0.5f, 90.0f) + 0.25f * bFbm(u * 8.0f, v * 8.0f - t * 0.5f);
        xGoldRamp(f, r, g, b);
        break;
    }
    case 21: {  // Gold sun rays
        float d = bLen(x, y), ang = atan2f(y, x);
        float rays = bSm(0.35f, 0.95f, 0.5f + 0.5f * sinf(ang * 14.0f + t * 0.8f));
        float rays2 = bSm(0.6f, 1.0f, 0.5f + 0.5f * sinf(ang * 22.0f - t * 0.6f)) * 0.5f;
        float f = 0.1f + (rays + rays2) * 0.7f * (1.0f - 0.7f * bSm(0.0f, 0.7f, d)) + bSm(0.1f, 0.095f, d) * 0.9f
                + xGl(d - 0.125f, 4000.0f) * 0.8f + xGl(d, 25.0f) * 0.25f;
        xGoldRamp(f, r, g, b);
        break;
    }
    case 22: {  // Gold scales
        float d, idc;
        xScaleCell(u, v, 6.0f, d, idc);
        float f = 0.7f - 0.55f * bSm(0.15f, 0.5f, d) + 0.12f * idc + 0.2f * xGl(d - 0.47f, 700.0f);
        f += 0.4f * xGl(Fr(u * 0.6f + v * 0.8f - t * 0.2f) - 0.5f, 40.0f);
        xGoldRamp(f, r, g, b);
        break;
    }
    case 23: {  // Gold lightning
        float in = 0.0f;
        for (int i = 0; i < 3; i++) {
            float cx = 0.2f + 0.3f * i + 0.05f * sinf(v * 30.0f + Hh((int)(t * 6.0f), i) * 10.0f) + 0.035f * sinf(v * 80.0f + i);
            float d = fabsf(u - cx);
            bool on = Hh((int)(t * 8.0f), i, 3) > 0.5f;
            if (on) in += xGl(d, 6000.0f) + 0.3f * xGl(d, 350.0f);
        }
        float bg = 0.08f + 0.05f * sinf(t * 2.0f);
        xGoldRamp(bg + in * 1.1f, r, g, b);
        break;
    }
    case 24: {  // Gold fireworks
        float f = 0.06f;
        for (int k = 0; k < 3; k++) {
            float kk = t * 0.3f + k * 0.33f;
            int cyc = (int)floorf(kk);
            float T = kk - cyc;
            float cx = 0.2f + 0.6f * Hh(cyc, k, 71), cy = 0.2f + 0.4f * Hh(cyc, k, 72);
            float dx = u - cx, dy = v - cy - T * T * 0.12f;
            float d = bLen(dx, dy), ang = atan2f(dy, dx);
            float rr = T * 0.3f;
            float a = Fr(ang / kTau * 22.0f) - 0.5f;
            float spark = (xGl(d - rr, 3000.0f) + 0.5f * xGl(d - rr * 0.8f, 3000.0f)) * xGl(a, 300.0f) * (1.0f - T);
            f += spark * 1.1f + xGl(d, 1500.0f) * (1.0f - T) * (T < 0.15f ? 1.0f : 0.0f);
        }
        xGoldRamp(f, r, g, b);
        break;
    }
    case 25: {  // Gold & emerald
        float a1 = u * 5.0f + v * 5.0f, a2 = u * 5.0f - v * 5.0f;
        float ln = Cl(xGl(xEdge(a1), 500.0f) + xGl(xEdge(a2), 500.0f));
        float h = Hh((int)floorf(a1), (int)floorf(a2), 9);
        float ec = 0.35f + 0.5f * h * (0.6f + 0.4f * sinf(t + h * 20.0f));
        float er = 0.02f + 0.06f * ec, eg = 0.25f + 0.4f * ec, eb = 0.12f + 0.2f * ec;
        float gr, gg, gb;
        xGoldRamp(0.55f + 0.4f * xGl(Fr(u * 0.6f + v * 0.4f - t * 0.2f) - 0.5f, 30.0f), gr, gg, gb);
        r = bMix(er, gr, ln); g = bMix(eg, gg, ln); b = bMix(eb, gb, ln);
        break;
    }
    case 26: {  // Gold stripes
        float w = (u * 0.8f + v * 0.6f) * 5.0f - t * 0.3f;
        int idx = (int)floorf(w);
        float s = Fr(w);
        float edge = bSm(0.0f, 0.06f, s) * bSm(1.0f, 0.94f, s);
        float shade = 0.28f + 0.6f * sinf(s * kPiX) * (0.7f + 0.3f * Hh(idx, 15));
        xGoldRamp(bMix(0.03f, shade, edge), r, g, b);
        break;
    }
    case 27: {  // Gold night stars
        xGoldRamp(0.07f + 0.05f * v, r, g, b);
        float s = xStar(u, v, 34.0f, 81, t) * 1.3f;
        float uu = u * 7.0f, vv = v * 7.0f;
        int ci = (int)floorf(uu), cj = (int)floorf(vv);
        float h = Hh(ci, cj, 82);
        if (h > 0.45f) {
            float dx = uu - ci - (0.25f + 0.5f * Hh(ci, cj, 83)), dy = vv - cj - (0.25f + 0.5f * Hh(ci, cj, 84));
            float tw = 0.5f + 0.5f * sinf(t * (1.0f + 2.0f * h) + h * 50.0f);
            float cross = expf(-dx * dx * 1200.0f - dy * dy * 14.0f) + expf(-dy * dy * 1200.0f - dx * dx * 14.0f);
            float core = expf(-(dx * dx + dy * dy) * 140.0f);
            s += (cross * 0.7f + core * 1.2f) * tw;
        }
        r += s; g += s * 0.8f; b += s * 0.35f;
        break;
    }
    default: {  // 28 Gold mirror
        float d1 = bLen(x - 0.2f * sinf(t * 0.6f), y - 0.2f * cosf(t * 0.5f));
        float d2 = bLen(x + 0.25f * cosf(t * 0.4f + 1.0f), y + 0.2f * sinf(t * 0.7f));
        float h = sinf(d1 * 34.0f - t * 3.0f) * expf(-d1 * 2.0f) + sinf(d2 * 28.0f - t * 2.5f) * expf(-d2 * 2.2f);
        float sp = Cl(h * 0.6f);
        float f = 0.5f + 0.3f * h + 0.5f * sp * sp * sp + 0.15f * (0.5f - v);
        xGoldRamp(f, r, g, b);
        break;
    }
    }
}

// ======================= v1.1: PARTY / SCENES / SODA (61 new, ids 261..321; drawn at 128x128 and doubled) =======================
// Party 261-282 (22) | Scenes 283-300 (18) | Soda 301-321 (21)
// -> Party, Scenes and Soda now have 32 designs each = at least 4 full pages in the menu.
static const int X_PARTY0 = 261, X_SCENE0 = 283, X_SODA0 = 301, X_V11_END = 322;
static inline float yRot(float& px, float& py, float a) {   // rotate (px,py) by a, returns the new py
    float c = cosf(a), s = sinf(a), nx = px * c + py * s, ny = -px * s + py * c;
    px = nx; py = ny; return ny;
}
static inline void yAdd(float& r, float& g, float& b, float h, float k) {   // add a hue colour * k
    float hr, hg, hb; Hsv(h, 1.0f, 1.0f, hr, hg, hb);
    r += hr * k; g += hg * k; b += hb * k;
}

// ---------------------------------------- PARTY (22) ----------------------------------------
static void YParty(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.02f;
    float x = u - 0.5f, y = v - 0.5f;
    float hr, hg, hb;
    switch (id) {
    case 0: {   // Disco ball
        float d = bLen(x, y), R = 0.3f;
        r = 0.02f + 0.03f * v; g = 0.01f; b = 0.05f + 0.05f * v;
        for (int i = 0; i < 6; i++) {
            float a = t * 0.5f * (1.0f + 0.2f * i) + i * 1.05f;
            float sx = 0.5f + 0.45f * cosf(a * 1.3f + i), sy = 0.5f + 0.45f * sinf(a + i * 2.0f);
            yAdd(r, g, b, i / 6.0f + t * 0.05f, xGl(bLen(u - sx, v - sy), 260.0f) * 0.7f);
        }
        if (fabsf(x) < 0.004f && y < -R && y > -0.5f) { r = g = b = 0.5f; }
        if (d < R) {
            float sx = x / R, sy = y / R;
            float nz = sqrtf(Cl(1.0f - sx * sx - sy * sy));
            float lon = atan2f(sx, nz) + t * 0.9f, lat = asinf(sy > 0.999f ? 0.999f : (sy < -0.999f ? -0.999f : sy));
            float fu = lon * 1.9099f, fv = lat * 1.9099f;
            int ci = (int)floorf(fu), cj = (int)floorf(fv);
            float h = Hh(ci, cj, 5);
            float gap = bMin(xEdge(fu), xEdge(fv));
            float sp = powf(0.5f + 0.5f * sinf(t * 3.0f + h * 40.0f), 8.0f);
            float lit = (0.25f + 0.55f * h) * (0.35f + 0.65f * nz);
            float m = bSm(0.03f, 0.1f, gap);
            Hsv(h * 0.3f + t * 0.05f + 0.55f, 0.35f, 1.0f, hr, hg, hb);
            float e = bSm(R, R - 0.012f, d);
            r = bMix(r, (hr * lit + sp) * m, e); g = bMix(g, (hg * lit + sp) * m, e); b = bMix(b, (hb * lit + sp) * m, e);
        }
        break;
    }
    case 1: {   // Laser fan
        float dx = u - 0.5f, dy = v - 1.08f;
        float ang = atan2f(dx, -dy);
        float fog = 0.03f + 0.05f * bFbm(u * 5.0f + t * 0.2f, v * 5.0f);
        r = fog * 0.6f; g = fog * 0.4f; b = fog;
        for (int i = 0; i < 7; i++) {
            float ai = (i - 3) * 0.24f + 0.3f * sinf(t * 1.1f + i * 0.9f);
            float dd = ang - ai;
            float k = xGl(dd, 7000.0f) * (0.6f + 0.4f * v) * 1.4f + 0.12f * xGl(dd, 300.0f) * v;
            yAdd(r, g, b, i / 7.0f + t * 0.07f, k);
        }
        float f2 = xGl(bLen(dx * 0.6f, dy + 0.04f), 14.0f) * 0.5f;
        r += f2; g += f2; b += f2;
        break;
    }
    case 2: {   // Glow sticks
        float su = u * 4.0f, sv = v * 4.0f;
        int ci = (int)floorf(su), cj = (int)floorf(sv);
        float h = Hh(ci, cj, 21);
        float px = su - ci - 0.5f, py = sv - cj - 0.5f;
        yRot(px, py, h * 6.2832f + t * (h - 0.5f) * 2.0f);
        float d = xBox(px, py, 0.3f, 0.05f);
        float core = bSm(0.012f, -0.012f, d), gl = xGl(d, 90.0f) * 0.6f;
        Hsv(Hh(ci, cj, 22) + t * 0.05f, 1.0f, 1.0f, hr, hg, hb);
        float band = 0.8f + 0.2f * sinf(px * 50.0f);
        r = 0.02f + hr * (gl + core * band) + core * 0.35f; g = 0.02f + hg * (gl + core * band) + core * 0.35f; b = 0.02f + hb * (gl + core * band) + core * 0.35f;
        break;
    }
    case 3: {   // Rising balloons
        r = 0.10f + 0.1f * v; g = 0.05f + 0.05f * v; b = 0.30f + 0.2f * v;
        for (int i = 0; i < 8; i++) {
            float h = Hh(i, 3, 31);
            float by = 1.25f - Fr(t * (0.06f + 0.06f * h) + h * 3.0f) * 1.5f;
            float bx = (i + 0.5f) / 8.0f + 0.03f * sinf(t * 1.3f + i * 2.0f);
            float sc = 0.8f + 0.5f * Hh(i, 4, 31);
            float e = bEll(u, v, bx, by, 0.055f * sc, 0.07f * sc);
            float str = bSm(0.004f, 0.0f, fabsf(u - bx - 0.01f * sinf(v * 30.0f + t * 3.0f))) * (v > by + 0.07f * sc && v < by + 0.3f ? 0.6f : 0.0f);
            r += str; g += str; b += str;
            if (e < 0.0f) {
                float lit = 0.6f + 0.4f * Cl(1.0f - bLen((u - bx + 0.02f) / (0.055f * sc), (v - by + 0.025f) / (0.07f * sc)));
                Hsv(h * 1.7f, 0.85f, lit, hr, hg, hb);
                float hl = bSm(0.35f, 0.0f, bLen((u - bx + 0.022f) / (0.055f * sc) * 2.0f, (v - by + 0.03f) / (0.07f * sc) * 2.0f));
                r = hr + hl * 0.5f; g = hg + hl * 0.5f; b = hb + hl * 0.5f;
            }
        }
        break;
    }
    case 4: {   // Firework bursts
        r = 0.01f; g = 0.01f; b = 0.04f + 0.03f * v;
        for (int k = 0; k < 3; k++) {
            float T = Fr(t * 0.3f + k / 3.0f);
            int ep = (int)floorf(t * 0.3f + k / 3.0f);
            float cx = 0.2f + 0.6f * Hh(k, ep, 41), cy = 0.18f + 0.35f * Hh(k, ep, 42);
            float dx = u - cx, dy = v - cy - 0.25f * T * T;
            float d = bLen(dx, dy), rad = 0.04f + 0.32f * sqrtf(T);
            float an = atan2f(dy, dx);
            float rays = 0.35f + 0.65f * powf(0.5f + 0.5f * cosf(an * 16.0f + k), 3.0f);
            float k1 = xGl(d - rad, 1800.0f) * (1.0f - T) * rays;
            float core = xGl(d, 200.0f) * bSm(0.12f, 0.0f, T) * 2.0f;
            float spk = Hh((int)(u * 70), (int)(v * 70), (int)(t * 10)) > 0.97f ? (1.0f - T) * xGl(d - rad * 0.8f, 40.0f) * 2.0f : 0.0f;
            yAdd(r, g, b, Hh(k, ep, 43), k1 * 1.3f);
            r += core + spk; g += core + spk; b += core + spk;
        }
        break;
    }
    case 5: {   // Stage spotlights
        float fl = 0.06f + 0.05f * v;
        r = fl * 0.7f; g = fl * 0.5f; b = fl;
        for (int i = 0; i < 3; i++) {
            float ox = 0.17f + 0.33f * i;
            float ang = atan2f(u - ox, v + 0.05f);
            float tg = 0.55f * sinf(t * 0.9f + i * 2.1f);
            float a = bSm(0.17f, 0.04f, fabsf(ang - tg)) * (1.0f - 0.45f * v);
            yAdd(r, g, b, i / 3.0f + t * 0.05f, a * 0.75f);
            float fx = ox + (0.05f + 0.95f * 0.82f) * tanf(tg) * 1.0f;
            float sp = xGl(bLen((u - fx) * 1.0f, (v - 0.9f) * 3.0f), 60.0f);
            yAdd(r, g, b, i / 3.0f + t * 0.05f, sp * 0.6f);
        }
        break;
    }
    case 6: {   // Dance floor
        float su = u * 6.0f, sv = v * 6.0f;
        int ci = (int)floorf(su), cj = (int)floorf(sv);
        float fx = su - ci, fy = sv - cj;
        float wave = 0.5f + 0.5f * sinf((ci + cj) * 0.9f - t * 4.0f);
        float h = Hh(ci, cj, (int)(t * 1.5f + wave * 2.0f));
        float edge = bMin(bMin(fx, 1.0f - fx), bMin(fy, 1.0f - fy));
        float bev = bSm(0.0f, 0.12f, edge);
        float val = (0.2f + 0.8f * wave) * (0.5f + 0.5f * bev);
        Hsv(h, 0.9f, val, r, g, b);
        float gl = xGl(bLen(fx - 0.5f, fy - 0.5f), 8.0f) * 0.25f * wave;
        r += gl; g += gl; b += gl;
        break;
    }
    case 7: {   // Streamers
        r = 0.05f; g = 0.03f; b = 0.08f;
        for (int i = 0; i < 9; i++) {
            float cx = (i + 0.5f) / 9.0f + 0.07f * sinf(v * 9.0f + t * 1.6f + i * 1.7f);
            float w = 0.016f + 0.01f * sinf(v * 25.0f + i);
            float k = bSm(w, w * 0.3f, fabsf(u - cx));
            float sh = 0.55f + 0.45f * sinf(v * 28.0f - t * 3.0f + i);
            Hsv(i / 9.0f + 0.02f * t, 0.85f, sh, hr, hg, hb);
            r = bMix(r, hr, k); g = bMix(g, hg, k); b = bMix(b, hb, k);
        }
        break;
    }
    case 8: {   // Sparklers
        for (int j = 0; j < 2; j++) {
            float su = u * 3.0f + j * 0.5f, sv = v * 3.0f + j * 0.3f;
            int ci = (int)floorf(su), cj = (int)floorf(sv);
            float h = Hh(ci, cj, 51 + j);
            float dx = su - ci - 0.5f, dy = sv - cj - 0.5f, d = bLen(dx, dy);
            float an = atan2f(dy, dx);
            float rays = powf(fabsf(cosf(an * 9.0f + h * 10.0f + t * (1.0f + h) * 2.0f)), 10.0f);
            float fl = 0.5f + 0.5f * sinf(t * 9.0f + h * 30.0f);
            float k = (xGl(d, 22.0f) * rays * 1.2f + xGl(d, 400.0f) * 1.5f) * (0.55f + 0.45f * fl);
            float sp = Hh((int)(u * 60), (int)(v * 60), (int)(t * 8) + j) > 0.985f ? xGl(d, 6.0f) : 0.0f;
            r += (k + sp) * 1.0f; g += (k + sp) * (0.7f + 0.2f * h); b += (k + sp) * (0.25f + 0.3f * h);
        }
        break;
    }
    case 9: {   // Rainbow checker waves
        float uu = u + 0.04f * sinf(v * 8.0f + t * 2.0f), vv = v + 0.04f * sinf(u * 8.0f + t * 2.3f);
        int ck = ((int)floorf(uu * 8.0f) + (int)floorf(vv * 8.0f)) & 1;
        Hsv(uu + vv + t * 0.2f, 0.9f, ck ? 1.0f : 0.3f, r, g, b);
        break;
    }
    case 10: {   // Strobe burst
        float T = Fr(t * 1.6f);
        int ep = (int)floorf(t * 1.6f);
        float flash = powf(1.0f - T, 4.0f);
        float an = atan2f(y, x), d = bLen(x, y);
        float rays = 0.4f + 0.6f * powf(0.5f + 0.5f * cosf(an * 10.0f + ep * 2.0f), 2.0f);
        Hsv(Hh(ep, 1, 61), 0.9f, 1.0f, hr, hg, hb);
        float k = flash * (rays * (1.0f - d * 0.8f) + xGl(d, 12.0f));
        r = 0.03f + hr * k; g = 0.03f + hg * k; b = 0.04f + hb * k;
        r += flash * flash * 0.5f; g += flash * flash * 0.5f; b += flash * flash * 0.5f;
        break;
    }
    case 11: {   // Beat rings
        float d = bLen(x, y), an = atan2f(y, x);
        float beat = powf(Fr(t * 1.5f), 3.0f);
        float q = Fr(d * 5.0f - t * 1.2f - beat * 0.3f);
        float seg = 0.5f + 0.5f * (sinf(an * 8.0f + t * 2.0f * ((int)(d * 5.0f - t * 1.2f) & 1 ? 1.0f : -1.0f)) > 0.0f ? 1.0f : -1.0f) * 0.9f;
        float in = (0.1f + 0.9f * xBell(q, 0.3f, 0.2f)) * seg * (1.0f + 0.5f * (1.0f - beat));
        Hsv(d * 0.9f + t * 0.1f, 1.0f, Cl(in), r, g, b);
        break;
    }
    case 12: {   // Lava lamp
        float f = 0.0f;
        for (int i = 0; i < 6; i++) {
            float h = Hh(i, 7, 71);
            float cy = 0.5f - 0.55f * cosf(t * (0.2f + 0.15f * h) + h * 20.0f) * 1.0f;
            float cx = 0.5f + 0.25f * sinf(t * 0.3f + h * 9.0f);
            float rr = 0.07f + 0.05f * h;
            float dd = bLen(u - cx, (v - cy) * 0.8f);
            f += rr * rr / (dd * dd + 0.0004f);
        }
        float bgk = 0.2f + 0.3f * v;
        r = 0.25f * bgk + 0.1f; g = 0.03f; b = 0.35f * bgk + 0.15f;
        float m = bSm(0.9f, 1.1f, f);
        float h2 = Cl((f - 1.0f) * 0.4f);
        r = bMix(r, 1.0f, m); g = bMix(g, 0.25f + 0.5f * h2, m); b = bMix(b, 0.25f - 0.1f * h2, m);
        float rim = xGl(f - 1.0f, 8.0f) * 0.25f * (1.0f - m);
        r += rim; g += rim * 0.5f;
        break;
    }
    case 13: {   // Kaleidoscope
        float an = atan2f(y, x), rr = bLen(x, y);
        float seg = 6.2832f / 8.0f;
        float a2 = fabsf(nMod(an, seg) - seg * 0.5f);
        float px = rr * cosf(a2), py = rr * sinf(a2);
        float p = sinf(px * 16.0f + t * 1.5f) + sinf(py * 14.0f - t * 1.2f) + sinf(rr * 20.0f - t * 2.0f);
        Hsv(0.5f + 0.2f * p + t * 0.05f, 0.85f, 0.35f + 0.65f * Cl(0.5f + 0.35f * p), r, g, b);
        break;
    }
    case 14: {   // Bubblegum swirl
        float an = atan2f(y, x), rr = bLen(x, y);
        float s = sinf(an * 3.0f + rr * 11.0f - t * 1.5f), s2 = sinf(an * 5.0f - rr * 7.0f + t);
        float m = bSm(-0.2f, 0.2f, s);
        r = bMix(1.0f, 1.0f, m); g = bMix(0.3f, 0.65f, m); b = bMix(0.62f, 0.85f, m);
        float l = bSm(0.04f, 0.0f, fabsf(s2));
        r = bMix(r, 0.5f, l * 0.6f); g = bMix(g, 0.95f, l * 0.6f); b = bMix(b, 1.0f, l * 0.6f);
        float hl = powf(Cl(0.5f + 0.5f * cosf(an - t * 0.7f)), 6.0f) * bSm(0.5f, 0.1f, rr) * 0.35f;
        r += hl; g += hl; b += hl;
        break;
    }
    case 15: {   // Glitter rain
        r = 0.02f; g = 0.01f; b = 0.05f;
        float nx = u * 26.0f;
        int ci = (int)floorf(nx);
        float h = Hh(ci, 1, 81), dx = Fr(nx) - 0.5f;
        float ph = Fr(v + t * (0.15f + 0.5f * h) + h * 5.0f);
        float tr = powf(1.0f - ph, 7.0f);
        float k = tr * xGl(dx, 40.0f) * (0.5f + 0.5f * sinf(t * 20.0f + h * 50.0f));
        yAdd(r, g, b, h + t * 0.1f, k * 1.2f);
        float s = xStar(u, v, 20.0f, 9, t * 2.0f);
        r += s; g += s; b += s;
        break;
    }
    case 16: {   // Marquee bulbs
        float su = u * 9.0f, sv = v * 9.0f;
        int ci = (int)floorf(su), cj = (int)floorf(sv);
        float ph = Fr((ci + cj) * 0.11f - t * 1.3f);
        float on = ph < 0.3f ? 1.0f : 0.12f;
        float d = bLen(Fr(su) - 0.5f, Fr(sv) - 0.5f);
        float core = bSm(0.2f, 0.12f, d), gl = xGl(d, 14.0f);
        bool warm = ((ci + cj) & 1) == 0;
        float cr = warm ? 1.0f : 1.0f, cg = warm ? 0.78f : 0.2f, cb = warm ? 0.3f : 0.2f;
        r = 0.04f + on * (cr * core + cr * gl * 0.5f); g = 0.03f + on * (cg * core + cg * gl * 0.5f); b = 0.03f + on * (cb * core + cb * gl * 0.5f);
        break;
    }
    case 17: {   // Pinata burst
        float d = bLen(x, y), an = atan2f(y, x);
        r = 0.05f; g = 0.02f; b = 0.07f;
        int n = 22;
        float fa = (an + 3.14159265f) / 6.2832f * n;
        int i0 = (int)floorf(fa);
        for (int di = -1; di <= 1; di++) {
            int i = i0 + di; int ii = ((i % n) + n) % n;
            float h = Hh(ii, 2, 91);
            float ac = (ii + 0.5f) / n * 6.2832f - 3.14159265f;
            float dist = Fr(t * (0.18f + 0.15f * h) + h * 4.0f) * 0.7f;
            float cx = cosf(ac) * dist, cy = sinf(ac) * dist + dist * dist * 0.25f;
            float sz = 0.018f + 0.02f * Hh(ii, 3, 91);
            float k = bSm(sz, sz * 0.5f, bLen(x - cx, y - cy));
            Hsv(h * 3.0f, 0.85f, 1.0f, hr, hg, hb);
            r = bMix(r, hr, k); g = bMix(g, hg, k); b = bMix(b, hb, k);
        }
        break;
    }
    case 18: {   // Rave tunnel
        float px = x, py = y;
        yRot(px, py, t * 0.25f);
        float d = bMax(fabsf(px), fabsf(py)) + 0.01f;
        float z = 0.18f / d + t * 0.9f;
        float q = Fr(z);
        float line = xGl(q - 0.5f, 90.0f) + 0.1f;
        float fog = Cl(d * 3.0f);
        Hsv(z * 0.15f + t * 0.1f, 1.0f, Cl(line) * fog, r, g, b);
        float cs = (((int)floorf(z) & 1) ? 0.15f : 0.0f) * fog;
        r += cs; g += cs * 0.5f; b += cs;
        break;
    }
    case 19: {   // Holo foil
        float h = u * 0.6f + v * 0.4f + 0.12f * sinf(u * 9.0f + t) + 0.12f * sinf(v * 7.0f - t * 1.2f) + t * 0.12f;
        float st = 0.5f + 0.5f * sinf((u - v) * 40.0f + t * 2.0f);
        Hsv(h, 0.55f, 0.55f + 0.35f * st, r, g, b);
        float sp = Hh((int)(u * 64), (int)(v * 64), (int)(t * 6)) > 0.985f ? 1.0f : 0.0f;
        r += sp; g += sp; b += sp;
        break;
    }
    case 20: {   // Vinyl record
        float d = bLen(x, y), an = atan2f(y, x);
        r = g = b = 0.04f + 0.04f * v;
        if (d < 0.46f) {
            float gr = 0.07f + 0.04f * sinf(d * 420.0f);
            float sh = powf(Cl(cosf((an - t * 1.6f) * 2.0f)), 10.0f) * 0.28f;
            r = g = b = gr + sh;
            if (d < 0.16f) {
                float sp = 0.5f + 0.5f * sinf(an * 3.0f + d * 30.0f - t * 1.6f);
                Hsv(0.92f + 0.12f * sp, 0.8f, 0.95f, r, g, b);
                if (d < 0.02f) r = g = b = 0.05f;
            }
            float e = bSm(0.46f, 0.452f, d);
            r *= e; g *= e; b *= e;
        }
        break;
    }
    default: {   // 21 Floor spots
        r = 0.04f; g = 0.02f; b = 0.07f;
        int ck = ((int)floorf(u * 8.0f) + (int)floorf(v * 8.0f)) & 1;
        float bg = ck ? 0.1f : 0.05f;
        r += bg * 0.6f; g += bg * 0.4f; b += bg;
        for (int i = 0; i < 5; i++) {
            float a = t * (0.35f + 0.1f * i) + i * 1.3f;
            float cx = 0.5f + 0.38f * cosf(a * 1.1f + i), cy = 0.5f + 0.38f * sinf(a * 0.9f + i * 2.0f);
            float d = bLen(u - cx, v - cy);
            float k = bSm(0.2f, 0.12f, d) * 0.55f + xGl(d - 0.16f, 900.0f) * 0.4f;
            yAdd(r, g, b, i / 5.0f + t * 0.08f, k);
        }
        break;
    }
    }
}

// ---------------------------------------- SCENES (18) ----------------------------------------
static inline void ySky(float v, float t0r, float t0g, float t0b, float b0r, float b0g, float b0b, float& r, float& g, float& b) {
    float k = Cl(v);
    r = bMix(t0r, b0r, k); g = bMix(t0g, b0g, k); b = bMix(t0b, b0b, k);
}
static inline float yMoon(float u, float v, float cx, float cy, float R, float& r, float& g, float& b) {   // adds a moon with glow, returns its coverage
    float d = bLen(u - cx, v - cy);
    float gl = xGl(d, 14.0f / (R * R * 100.0f) * 6.0f) * 0.35f;
    r += gl * 0.8f; g += gl * 0.85f; b += gl;
    float m = bSm(R, R - 0.008f, d);
    float cr = 0.92f - 0.12f * bFbm((u - cx) * 14.0f / R * 0.1f + 3.0f, (v - cy) * 14.0f / R * 0.1f);
    bPut(r, g, b, cr, cr * 0.97f, cr * 0.85f, m);
    return m;
}
static void YScene(int id, float u, float v, float t, float& r, float& g, float& b) {
    float x = u - 0.5f, y = v - 0.5f;
    float hr, hg, hb;
    switch (id) {
    case 0: {   // Lighthouse in the storm
        ySky(v, 0.02f, 0.03f, 0.10f, 0.10f, 0.12f, 0.22f, r, g, b);
        float cl = bFbm(u * 3.0f + t * 0.05f, v * 3.0f);
        r += cl * 0.05f; g += cl * 0.05f; b += cl * 0.08f;
        xAddStars(r, g, b, xStar(u, v, 16.0f, 3, t) * 0.5f);
        float lx = 0.5f, ly = 0.27f;
        float L = cosf(t * 0.9f);
        float dx = u - lx, dy = v - ly;
        float dxs = dx * (L > 0.0f ? 1.0f : -1.0f);
        if (dxs > 0.0f && dxs < 0.55f * fabsf(L) + 0.05f) {
            float a = bSm(0.015f + 0.09f * dxs, 0.0f, fabsf(dy + dxs * 0.03f)) * (1.0f - dxs * 1.3f * fabsf(L)) * (0.6f + 0.4f * fabsf(L));
            r += a * 0.9f; g += a * 0.85f; b += a * 0.6f;
        }
        float sea = 0.74f + 0.012f * sinf(u * 20.0f + t * 2.0f) + 0.008f * sinf(u * 47.0f - t * 3.0f);
        if (v > sea) {
            float w = 0.5f + 0.5f * sinf(u * 30.0f + v * 60.0f - t * 3.0f);
            bPut(r, g, b, 0.03f + 0.05f * w, 0.08f + 0.08f * w, 0.16f + 0.1f * w, 1.0f);
            float foam = bSm(0.02f, 0.0f, v - sea) * (0.6f + 0.4f * sinf(u * 60.0f + t * 4.0f));
            r += foam * 0.7f; g += foam * 0.75f; b += foam * 0.8f;
        }
        float rock = 0.76f - 0.07f * bSm(0.3f, 0.0f, fabsf(u - 0.5f)) - 0.02f * bFbm(u * 14.0f, 2.0f);
        if (v > rock && fabsf(u - 0.5f) < 0.3f) bPut(r, g, b, 0.07f, 0.07f, 0.09f, 1.0f);
        float hw = 0.04f + 0.035f * (v - 0.33f) / 0.4f;
        if (v > 0.33f && v < 0.72f && fabsf(dx) < hw) {
            float st = (int)floorf(v * 13.0f) & 1;
            float sh = 0.55f + 0.45f * Cl(1.0f - (dx / hw + 1.0f) * 0.5f);
            bPut(r, g, b, st ? 0.85f * sh : 0.75f * sh, st ? 0.85f * sh : 0.1f * sh, st ? 0.85f * sh : 0.1f * sh, 1.0f);
        }
        if (v > 0.255f && v <= 0.33f && fabsf(dx) < 0.034f) { bPut(r, g, b, 1.0f, 0.95f, 0.6f, 1.0f); }
        if (v > 0.2f && v <= 0.255f && fabsf(dx) < 0.05f * (v - 0.2f) / 0.055f) bPut(r, g, b, 0.5f, 0.05f, 0.05f, 1.0f);
        float lg = xGl(bLen(dx, dy), 400.0f) * 1.5f;
        r += lg; g += lg * 0.9f; b += lg * 0.6f;
        float rn = Hh((int)(u * 90), (int)(v * 90 + t * 120.0f), 7) > 0.985f ? 0.4f : 0.0f;   // rain
        r += rn * 0.5f; g += rn * 0.6f; b += rn * 0.8f;
        break;
    }
    case 1: {   // Desert dunes and moon
        ySky(v, 0.10f, 0.07f, 0.28f, 0.95f, 0.45f, 0.30f, r, g, b);
        xAddStars(r, g, b, xStar(u, v, 18.0f, 5, t) * (1.0f - v * 1.6f > 0 ? 1.0f - v * 1.6f : 0.0f));
        yMoon(u, v, 0.72f, 0.24f, 0.1f, r, g, b);
        for (int k = 0; k < 3; k++) {
            float base = 0.55f + 0.12f * k;
            float ridge = base + 0.05f * sinf(u * (4.0f + k * 1.5f) + k * 2.0f) + 0.02f * sinf(u * 11.0f + k) - 0.03f * k * 0.0f;
            if (v > ridge) {
                float sh = 0.35f + 0.5f * Cl(0.5f + 0.5f * sinf(u * (4.0f + k * 1.5f) + k * 2.0f + 1.2f));
                float drift = 0.04f * sinf((u * 30.0f - t * 2.0f) + v * 60.0f) * (k + 1) * 0.5f;
                float c0 = (0.25f + 0.18f * k) * (sh + drift);
                bPut(r, g, b, c0 * 1.25f + 0.05f, c0 * 0.75f + 0.03f, c0 * 0.55f + 0.08f * (2 - k), 1.0f);
            }
        }
        float cu = Fr(t * 0.035f) * 1.4f - 0.2f;
        for (int c = 0; c < 3; c++) {
            float px = cu - c * 0.11f, base = 0.66f + 0.05f * sinf(px * 6.0f + 2.0f) + 0.02f * sinf(px * 11.0f + 1.0f);
            float bob = 0.004f * sinf(t * 4.0f + c);
            float d = bEll(u, v, px, base - 0.035f + bob, 0.04f, 0.018f);
            d = bMin(d, bEll(u, v, px - 0.012f, base - 0.058f + bob, 0.012f, 0.013f));
            d = bMin(d, bTap(u, v, px + 0.03f, base - 0.04f + bob, px + 0.052f, base - 0.07f + bob, 0.008f, 0.005f));
            d = bMin(d, bCap(u, v, px - 0.025f, base - 0.02f + bob, px - 0.025f + 0.01f * sinf(t * 4 + c), base + 0.005f, 0.004f));
            d = bMin(d, bCap(u, v, px + 0.025f, base - 0.02f + bob, px + 0.025f - 0.01f * sinf(t * 4 + c), base + 0.005f, 0.004f));
            bPut(r, g, b, 0.05f, 0.03f, 0.06f, bEdge(d));
        }
        break;
    }
    case 2: {   // Cherry blossom
        ySky(v, 1.0f, 0.82f, 0.88f, 1.0f, 0.93f, 0.9f, r, g, b);
        float sun = xGl(bLen(u - 0.8f, v - 0.2f), 30.0f) * 0.35f;
        r += sun; g += sun * 0.8f; b += sun * 0.7f;
        float by = 0.18f + 0.35f * u + 0.03f * sinf(u * 9.0f);
        float bd = fabsf(v - by) - 0.018f * (1.2f - u * 0.6f);
        float bd2 = fabsf(v - (by + 0.28f * (u - 0.35f) + 0.04f)) - 0.01f;
        if (u > 0.35f) bd = bMin(bd, bd2);
        bPut(r, g, b, 0.22f, 0.12f, 0.12f, bEdge(bd));
        for (int s = 0; s < 2; s++) {
            float su = u * (9.0f + 4.0f * s), sv = v * (9.0f + 4.0f * s);
            int ci = (int)floorf(su), cj = (int)floorf(sv);
            float h = Hh(ci, cj, 101 + s);
            float cx = ci + 0.3f + 0.4f * Hh(ci, cj, 103), cy = cj + 0.3f + 0.4f * Hh(ci, cj, 104);
            float dens = bSm(0.32f, 0.0f, fabsf(v - by - 0.03f * s));
            if (h < dens * 1.4f) {
                float d = bLen(su - cx, sv - cy);
                float an = atan2f(sv - cy, su - cx);
                float petal = 0.28f * (0.75f + 0.25f * cosf(an * 5.0f + h * 6.0f));
                float k = bSm(petal, petal - 0.06f, d);
                float c = 0.9f + 0.1f * Hh(ci, cj, 105);
                bPut(r, g, b, c, 0.55f + 0.2f * h, 0.7f + 0.15f * h, k * (s ? 0.75f : 1.0f));
                bPut(r, g, b, 0.9f, 0.2f, 0.3f, bSm(0.05f, 0.0f, d) * 0.7f * k);
            }
        }
        for (int i = 0; i < 12; i++) {
            float h = Hh(i, 5, 111);
            float py = Fr(t * (0.07f + 0.05f * h) + h * 7.0f) * 1.2f - 0.1f;
            float px = Fr(h * 3.7f + 0.2f * py + 0.04f * sinf(t * 1.5f + h * 20.0f) + t * 0.01f);
            float lx = u - px, ly = v - py;
            yRot(lx, ly, t * 2.0f * (h - 0.5f) + h * 6.0f);
            float k = bSm(0.016f, 0.008f, bLen(lx * 1.0f, ly * 2.4f));
            bPut(r, g, b, 1.0f, 0.68f, 0.8f, k);
        }
        break;
    }
    case 3: {   // Erupting volcano
        ySky(v, 0.03f, 0.02f, 0.06f, 0.35f, 0.08f, 0.04f, r, g, b);
        float gl = xGl(bLen(u - 0.5f, v - 0.4f), 5.0f) * 0.45f;
        r += gl; g += gl * 0.35f; b += gl * 0.1f;
        float cl = bFbm(u * 4.0f - 1.0f, v * 4.0f - t * 0.5f) * bSm(0.5f, 0.0f, fabsf(u - 0.5f - 0.08f * (0.5f - v))) * bSm(0.45f, 0.1f, v);
        r = bMix(r, 0.18f + gl, cl * 0.9f); g = bMix(g, 0.12f + gl * 0.3f, cl * 0.9f); b = bMix(b, 0.12f, cl * 0.9f);
        for (int i = 0; i < 9; i++) {
            float h = Hh(i, 6, 121);
            float T = Fr(t * 0.35f + h);
            float vx = (h - 0.5f) * 0.9f * T;
            float px = 0.5f + vx, py = 0.4f - 0.55f * T * (1.0f - T) * 2.0f * (0.6f + 0.6f * Hh(i, 7, 121)) + 0.0f;
            float k = xGl(bLen(u - px, v - py), 2500.0f) * 2.0f * (1.0f - T * 0.5f);
            r += k; g += k * 0.55f; b += k * 0.15f;
        }
        float ridge = 0.42f + 1.35f * fabsf(u - 0.5f) * (0.9f + 0.1f * sinf(u * 19.0f));
        if (v > ridge && v > 0.4f) {
            float rock = 0.5f + 0.5f * bFbm(u * 12.0f, v * 12.0f);
            bPut(r, g, b, 0.07f * rock, 0.05f * rock, 0.05f * rock, 1.0f);
            float fl = bFbm(u * 9.0f, v * 9.0f - t * 0.7f);
            float stream = bSm(0.07f, 0.0f, fabsf(u - 0.5f - 0.05f * sinf(v * 15.0f + t) * 1.0f - (v - 0.42f) * 0.32f)) * bSm(0.4f, 0.55f, v) * 0.0f;
            float s2 = bSm(0.04f, 0.0f, fabsf(u - 0.5f + 0.03f * sinf(v * 12.0f - t * 0.5f) + (v - 0.42f) * 0.4f));
            float s3 = bSm(0.035f, 0.0f, fabsf(u - 0.5f - 0.03f * sinf(v * 10.0f + t * 0.4f) - (v - 0.42f) * 0.55f));
            float lv = bMax(s2, s3) * (0.5f + 0.7f * fl) + stream;
            xHeat(lv * 1.1f, 0, hr, hg, hb);
            r += hr; g += hg; b += hb;
        }
        break;
    }
    case 4: {   // Pirate ship
        ySky(v, 0.03f, 0.04f, 0.16f, 0.22f, 0.25f, 0.45f, r, g, b);
        xAddStars(r, g, b, xStar(u, v, 16.0f, 3, t) * 0.7f);
        yMoon(u, v, 0.2f, 0.2f, 0.07f, r, g, b);
        float bob = 0.012f * sinf(t * 1.4f), tilt = 0.05f * sinf(t * 1.4f + 0.5f);
        float px = x, py = y - 0.07f - bob;
        yRot(px, py, tilt);
        float sh = 0.75f + 0.25f * sinf(px * 24.0f + t * 2.0f);
        float bulge = 0.02f * sinf(t * 1.2f);
        // sails (behind the hull)
        float s1 = xBox(px, py + 0.16f, 0.12f + bulge, 0.09f);
        float s2 = xBox(px, py + 0.31f, 0.09f + bulge, 0.06f);
        float s3 = xBox(px - 0.17f, py + 0.12f, 0.065f + bulge, 0.075f);
        float jib = bMax(xBox(px - 0.31f, py + 0.02f, 0.07f, 0.07f), (px - 0.24f) * 0.9f - (py + 0.1f) * 0.0f + (py + 0.09f) * -0.8f);
        float mast = bMin(bCap(px, py, 0.0f, 0.0f, 0.0f, -0.4f, 0.007f), bCap(px, py, 0.17f, 0.0f, 0.17f, -0.27f, 0.006f));
        mast = bMin(mast, bCap(px, py, 0.2f, 0.0f, 0.37f, -0.04f, 0.004f));
        mast = bMin(mast, bCap(px, py, -0.12f, -0.16f, 0.12f, -0.16f, 0.004f));
        mast = bMin(mast, bCap(px, py, -0.09f, -0.31f, 0.09f, -0.31f, 0.004f));
        bPut(r, g, b, 0.14f, 0.08f, 0.05f, bEdge(mast));
        bPut(r, g, b, 0.92f * sh, 0.86f * sh, 0.74f * sh, bEdge(bMin(bMin(s1, s2), s3)));
        float jb = bMax(bMax(px - 0.2f, 0.37f - px), bMax(-(py + 0.09f) , (py + 0.01f) - (0.37f - px) * -0.0f));
        float jd = bMax(bMax(px - 0.2f - 0.0f, -(px - 0.2f) * 0.0f - 1.0f), 1.0f);
        (void)jb; (void)jd; (void)jib; (void)jib;
        float tri = bMax(bMax(0.2f - px, px - 0.36f), (py + 0.1f) - (px - 0.2f) * -0.0f);
        float tri2 = bMax(bMax(0.21f - px, -(py + 0.1f)), (py + 0.02f) + (px - 0.21f) * -0.55f * -1.0f - 0.16f * 0.0f);
        (void)tri; (void)tri2;
        // hull: lower half ellipse + raised stern + bow
        float hull = bMax(bEll(px, py, 0.0f, 0.0f, 0.28f, 0.1f), -py);
        hull = bMin(hull, xBox(px + 0.22f, py + 0.01f, 0.06f, 0.025f));
        hull = bMin(hull, bTap(px, py, 0.26f, -0.005f, 0.33f, -0.03f, 0.012f, 0.004f));
        float wood = 0.5f + 0.5f * sinf(py * 120.0f);
        bPut(r, g, b, 0.22f + 0.05f * wood, 0.11f + 0.03f * wood, 0.05f, bEdge(hull));
        bPut(r, g, b, 0.85f, 0.65f, 0.15f, bEdge(hull) * bSm(0.006f, 0.0f, fabsf(py - 0.03f)) * 0.9f);
        for (int i = 0; i < 5; i++) {
            float k = bSm(0.011f, 0.007f, bLen(px + 0.14f - i * 0.07f, py - 0.05f)) * bEdge(hull);
            bPut(r, g, b, 0.02f, 0.02f, 0.02f, k);
        }
        // flag with skull
        float fy = py + 0.4f + 0.012f * sinf(px * 40.0f - t * 6.0f) - 0.0f;
        float flag = xBox(px - 0.04f, fy + 0.005f, 0.04f, 0.018f);
        bPut(r, g, b, 0.04f, 0.04f, 0.04f, bEdge(flag));
        bPut(r, g, b, 0.95f, 0.95f, 0.95f, bSm(0.009f, 0.006f, bLen(px - 0.04f, fy)) * bEdge(flag));
        // sea
        float sea = 0.64f + 0.015f * sinf(u * 14.0f + t * 1.8f) + 0.01f * sinf(u * 33.0f - t * 2.7f);
        if (v > sea) {
            float w = 0.5f + 0.5f * sinf(u * 22.0f + v * 40.0f - t * 2.0f);
            bPut(r, g, b, 0.03f + 0.04f * w, 0.1f + 0.08f * w, 0.2f + 0.1f * w, 1.0f);
            float refl = xGl(u - 0.2f + 0.03f * sinf(v * 50.0f + t * 2.0f), 150.0f) * 0.25f * bSm(0.64f, 0.9f, v);
            r += refl; g += refl; b += refl * 0.9f;
            float foam = bSm(0.012f, 0.0f, v - sea) * (0.5f + 0.5f * sinf(u * 50.0f + t * 4.0f));
            r += foam * 0.5f; g += foam * 0.55f; b += foam * 0.6f;
        }
        break;
    }
    case 5: {   // Rocket launch
        ySky(v, 0.02f, 0.03f, 0.12f, 0.35f, 0.5f, 0.85f, r, g, b);
        xAddStars(r, g, b, xStar(u, v, 20.0f, 4, t) * (1.0f - v));
        float ry = 0.95f - Fr(t * 0.1f) * 1.35f;
        float rx = 0.5f + 0.006f * sinf(t * 30.0f);
        if (v > 0.88f) bPut(r, g, b, 0.18f, 0.2f, 0.16f, 1.0f);
        float sm = bFbm(u * 6.0f, v * 4.0f - t * 1.5f);
        float sw = 0.03f + 0.2f * bSm(ry, 1.05f, v) * (v - ry);
        float smk = bSm(sw, sw * 0.4f, fabsf(u - rx) + (sm - 0.5f) * 0.05f) * bSm(ry + 0.1f, ry + 0.2f, v) * 0.75f * bSm(1.2f, 0.6f, v - ry);
        r = bMix(r, 0.85f, smk); g = bMix(g, 0.85f, smk); b = bMix(b, 0.88f, smk);
        float dx = u - rx, dy = v - ry;
        float body = bTap(u, v, rx, ry - 0.1f, rx, ry + 0.08f, 0.0f, 0.04f);
        body = bMin(body, bCap(u, v, rx, ry + 0.0f, rx, ry + 0.1f, 0.04f));
        body = bMin(body, xBox(dx, dy - 0.04f, 0.04f, 0.07f));
        float fins = bMax(bLen(dx - 0.0f, 0.0f) * 0.0f, bMax(fabsf(dx) - 0.075f * bSm(0.14f, 0.07f, dy) , -(dy - 0.14f)));
        fins = bMax(fins, dy - 0.15f); fins = bMax(fins, -(dy - 0.06f));
        bPut(r, g, b, 0.75f, 0.1f, 0.1f, bEdge(fins));
        float sh = 0.7f + 0.3f * Cl(1.0f - (dx + 0.04f) / 0.08f);
        bPut(r, g, b, 0.92f * sh, 0.92f * sh, 0.95f * sh, bEdge(body));
        bPut(r, g, b, 0.2f, 0.5f, 0.9f, bEdge(bLen(dx, dy - 0.01f) - 0.014f));
        bPut(r, g, b, 0.85f, 0.15f, 0.12f, bEdge(bTap(u, v, rx, ry - 0.1f, rx, ry - 0.05f, 0.0f, 0.04f)));
        float fl = 0.15f + 0.04f * sinf(t * 40.0f);
        float fd = bTap(u, v, rx, ry + 0.11f, rx, ry + 0.11f + fl, 0.03f, 0.0f);
        xHeat(bSm(0.03f, -0.03f, fd) * 1.3f, 0, hr, hg, hb);
        if (fd < 0.02f) { r = bMix(r, hr, bEdge(fd)); g = bMix(g, hg, bEdge(fd)); b = bMix(b, hb, bEdge(fd)); }
        float gl = xGl(bLen(dx, (dy - 0.15f) * 0.6f), 50.0f) * 0.5f;
        r += gl; g += gl * 0.6f; b += gl * 0.2f;
        break;
    }
    case 6: {   // Moonlit castle
        ySky(v, 0.03f, 0.03f, 0.12f, 0.2f, 0.12f, 0.3f, r, g, b);
        xAddStars(r, g, b, xStar(u, v, 18.0f, 4, t) * 0.9f);
        yMoon(u, v, 0.78f, 0.2f, 0.09f, r, g, b);
        float hill = 0.78f - 0.1f * bSm(0.6f, 0.0f, fabsf(u - 0.45f));
        float cd = xBox(u - 0.45f, v - 0.55f, 0.14f, 0.2f);
        cd = bMin(cd, xBox(u - 0.27f, v - 0.5f, 0.05f, 0.25f));
        cd = bMin(cd, xBox(u - 0.63f, v - 0.48f, 0.05f, 0.27f));
        float roof1 = bMax(fabsf(u - 0.27f) - 0.07f * bSm(0.17f, 0.3f, v) * 1.0f, 0.0f) ;
        float r1 = (fabsf(u - 0.27f) * 1.7f + (v - 0.22f) - 0.0f);
        float r2 = (fabsf(u - 0.63f) * 1.8f + (v - 0.18f) - 0.0f);
        float rf1 = (r1 < 0.12f * 1.0f && v < 0.26f && v > 0.14f) ? 1.0f : 0.0f;
        float rf2 = (r2 < 0.12f && v < 0.22f && v > 0.1f) ? 1.0f : 0.0f;
        bPut(r, g, b, 0.05f, 0.04f, 0.09f, bEdge(cd));
        r = bMix(r, 0.05f, rf1); g = bMix(g, 0.04f, rf1); b = bMix(b, 0.09f, rf1);
        r = bMix(r, 0.05f, rf2); g = bMix(g, 0.04f, rf2); b = bMix(b, 0.09f, rf2);
        float crn = ((int)floorf(u * 60.0f) & 1) ? 0.0f : 1.0f;
        if (v > 0.3f && v < 0.33f && u > 0.31f && u < 0.59f && crn > 0.5f) { r = 0.05f; g = 0.04f; b = 0.09f; }
        for (int i = 0; i < 6; i++) {
            float wx = 0.27f + (i % 3) * 0.18f, wy = 0.4f + (i / 3) * 0.15f;
            if (i % 3 == 1) wx = 0.45f + (i / 3) * 0.04f - 0.02f;
            float fl = 0.7f + 0.3f * sinf(t * (3.0f + i) + i * 4.0f);
            float d = xBox(u - wx, v - wy, 0.012f, 0.02f);
            bPut(r, g, b, 1.0f * fl, 0.75f * fl, 0.3f * fl, bEdge(d) * 0.95f);
        }
        if (v > hill) bPut(r, g, b, 0.02f, 0.03f, 0.05f, 1.0f);
        float mist = bFbm(u * 5.0f + t * 0.1f, v * 6.0f) * bSm(0.62f, 0.9f, v) * 0.45f;
        r += mist * 0.35f; g += mist * 0.3f; b += mist * 0.5f;
        for (int k = 0; k < 3; k++) {
            float bx = Fr(t * 0.05f + k * 0.33f) * 1.3f - 0.15f, by = 0.2f + 0.1f * sinf(t * 0.7f + k * 2.0f) + 0.05f * k;
            float fl = sinf(t * 12.0f + k * 3.0f);
            float d = bMin(bLen((u - bx) * 1.0f, (v - by) * 1.8f) - 0.008f, bCap(u, v, bx - 0.025f, by - 0.01f * fl, bx + 0.025f, by - 0.01f * fl, 0.004f + 0.004f * (1 - fabsf(fl))));
            bPut(r, g, b, 0.0f, 0.0f, 0.0f, bEdge(d));
        }
        break;
    }
    case 7: {   // Sunflower field
        ySky(v, 0.25f, 0.55f, 0.95f, 0.8f, 0.9f, 1.0f, r, g, b);
        float sd = bLen(u - 0.8f, v - 0.15f);
        bPut(r, g, b, 1.0f, 0.97f, 0.7f, bSm(0.07f, 0.06f, sd));
        r += xGl(sd, 12.0f) * 0.3f; g += xGl(sd, 12.0f) * 0.25f;
        float cl = bFbm(u * 4.0f + t * 0.03f, v * 8.0f) * bSm(0.45f, 0.1f, v);
        r = bMix(r, 1.0f, cl * 0.6f); g = bMix(g, 1.0f, cl * 0.6f); b = bMix(b, 1.0f, cl * 0.6f);
        float hz = 0.45f;
        if (v > hz) {
            float gk = 0.25f + 0.2f * bFbm(u * 20.0f, v * 30.0f);
            bPut(r, g, b, 0.1f + 0.1f * gk, 0.3f + 0.3f * gk, 0.08f, 1.0f);
            for (int row = 0; row < 3; row++) {
                float n = 5.0f + row * 2.5f * 0.0f + row * 1.0f;
                float sc = 1.0f + row * 0.5f * 0.0f;
                float rowV = 0.55f + 0.17f * row, off = 0.37f * row;
                float uu = u * n + off;
                int ci = (int)floorf(uu);
                float cx = ci + 0.5f + 0.15f * (Hh(ci, row, 131) - 0.5f);
                float sw = 0.05f * sinf(t * 1.1f + ci * 1.7f + row);
                float rad = (0.055f + 0.025f * row) * n * 0.2f * 5.0f / n;
                float fx = (uu - cx) / n, fy = v - (rowV - 0.0f);
                float stem = bSm(0.006f + 0.003f * row, 0.002f, fabsf(fx - sw * (rowV - v) * 2.0f)) * (v > rowV ? 1.0f : 0.0f);
                bPut(r, g, b, 0.1f, 0.35f, 0.08f, stem);
                float px = fx - sw * 0.0f, py = fy;
                float d = bLen(px, py), an = atan2f(py, px) + sw * 3.0f;
                float R = 0.05f + 0.022f * row;
                float petal = R * (1.0f + 0.42f * (0.5f + 0.5f * cosf(an * 12.0f)));
                float k = bSm(petal, petal - 0.012f, d);
                bPut(r, g, b, 1.0f, 0.78f - 0.1f * (d / R), 0.05f, k);
                float cd = bSm(R * 0.62f, R * 0.58f, d);
                float seed = 0.5f + 0.5f * sinf(an * 7.0f + d * 90.0f);
                bPut(r, g, b, 0.22f + 0.1f * seed, 0.12f + 0.05f * seed, 0.04f, cd);
            }
        }
        break;
    }
    case 8: {   // Windmill at sunset
        ySky(v, 0.35f, 0.15f, 0.45f, 1.0f, 0.55f, 0.15f, r, g, b);
        float sd = bLen(u - 0.25f, v - 0.58f);
        bPut(r, g, b, 1.0f, 0.85f, 0.45f, bSm(0.09f, 0.085f, sd));
        r += xGl(sd, 8.0f) * 0.4f; g += xGl(sd, 8.0f) * 0.2f;
        float cl = bFbm(u * 4.0f + t * 0.04f, v * 14.0f) * bSm(0.4f, 0.1f, v) * bSm(0.15f, 0.3f, v);
        r = bMix(r, 1.0f, cl * 0.35f); g = bMix(g, 0.55f, cl * 0.35f); b = bMix(b, 0.5f, cl * 0.35f);
        float h1 = 0.74f + 0.04f * sinf(u * 5.0f + 1.0f), h2 = 0.82f + 0.03f * sinf(u * 7.0f);
        if (v > h1) bPut(r, g, b, 0.28f, 0.1f, 0.2f, 1.0f);
        if (v > h2) bPut(r, g, b, 0.12f, 0.05f, 0.12f, 1.0f);
        float wx = 0.62f, wy = 0.42f;
        float tw = 0.045f + 0.04f * (v - wy) / 0.4f;
        float tower = (v > wy && v < 0.78f) ? fabsf(u - wx) - tw : 1.0f;
        bPut(r, g, b, 0.1f, 0.04f, 0.1f, bEdge(tower));
        float cap = bTap(u, v, wx, wy - 0.045f, wx, wy + 0.004f, 0.0f, 0.05f);
        bPut(r, g, b, 0.08f, 0.03f, 0.08f, bEdge(cap));
        float door = xBox(u - wx, v - 0.75f, 0.012f, 0.025f);
        bPut(r, g, b, 1.0f, 0.7f, 0.3f, bEdge(door));
        float bd = 9.0f;
        for (int i = 0; i < 4; i++) {
            float px = u - wx, py = v - wy;
            yRot(px, py, t * 0.7f + i * 1.5708f);
            float bl = xBox(px - 0.17f, py - 0.012f, 0.14f, 0.012f);
            float lat = xBox(px - 0.19f, py - 0.04f, 0.1f, 0.026f);
            bd = bMin(bd, bl);
            float lt = bSm(0.004f, 0.0f, fabsf(Fr(px * 22.0f) - 0.5f) * 0.045f - 0.0f) ;
            bPut(r, g, b, 0.1f, 0.04f, 0.1f, bEdge(bMax(lat, -0.0f)) * (0.5f + 0.5f * lt));
        }
        bPut(r, g, b, 0.08f, 0.03f, 0.08f, bEdge(bd));
        bPut(r, g, b, 0.08f, 0.03f, 0.08f, bEdge(bLen(u - wx, v - wy) - 0.014f));
        break;
    }
    case 9: {   // City skyline at night
        ySky(v, 0.03f, 0.02f, 0.12f, 0.45f, 0.15f, 0.4f, r, g, b);
        xAddStars(r, g, b, xStar(u, v, 20.0f, 4, t) * (1.0f - v * 1.5f > 0 ? 1.0f - v * 1.5f : 0.0f));
        yMoon(u, v, 0.8f, 0.17f, 0.06f, r, g, b);
        for (int L = 0; L < 2; L++) {
            float n = L ? 11.0f : 16.0f;
            float uu = u * n + L * 3.0f;
            int ci = (int)floorf(uu);
            float fx = uu - ci;
            float h = (L ? 0.22f : 0.12f) + (L ? 0.35f : 0.3f) * Hh(ci, L, 141);
            float top = 0.92f - h;
            if (v > top && fx > 0.06f && fx < 0.94f) {
                float c0 = L ? 0.07f : 0.025f;
                bPut(r, g, b, c0 + 0.02f, c0, c0 + 0.05f, 1.0f);
                float wu = fx * 4.0f, wv = (v - top) * n * 2.2f * (L ? 1.0f : 1.4f);
                int wi = (int)floorf(wu), wj = (int)floorf(wv);
                float on = Hh(ci * 7 + wi, wj + L * 50, 142 + (int)(t * 0.15f));
                if (on > (L ? 0.5f : 0.6f) && Fr(wu) > 0.2f && Fr(wu) < 0.8f && Fr(wv) > 0.25f && Fr(wv) < 0.75f) {
                    float w = 0.6f + 0.4f * Hh(wi, wj, ci);
                    float k = L ? 1.0f : 0.8f;
                    r = 1.0f * w * k; g = 0.8f * w * k; b = 0.4f * w * k;
                }
            }
            if (L == 1 && Hh(ci, 1, 143) > 0.7f && fx > 0.45f && fx < 0.55f && v > top - 0.07f && v <= top) {
                bPut(r, g, b, 0.07f, 0.07f, 0.12f, 1.0f);
            }
            if (L == 1 && Hh(ci, 1, 143) > 0.7f && bLen(u * n + 3.0f - ci - 0.5f, (v - (top - 0.075f)) * n) < 0.12f) {
                float bl = 0.5f + 0.5f * sinf(t * 3.0f + ci);
                r += bl; g += bl * 0.1f; b += bl * 0.1f;
            }
        }
        float fg = bSm(0.82f, 1.0f, v) * 0.25f;
        r += fg * 0.6f; g += fg * 0.3f; b += fg * 0.5f;
        break;
    }
    case 10: {   // Rainy neon window
        r = 0.02f; g = 0.02f; b = 0.05f;
        for (int L = 0; L < 2; L++) {
            float n = L ? 5.0f : 3.0f;
            float su = u * n + 0.37f * L, sv = v * n * 0.8f + 0.2f * L;
            int ci = (int)floorf(su), cj = (int)floorf(sv);
            float h = Hh(ci, cj, 151 + L);
            float cx = ci + 0.2f + 0.6f * Hh(ci, cj, 153), cy = cj + 0.2f + 0.6f * Hh(ci, cj, 154);
            float d = bLen(su - cx, sv - cy);
            float rad = 0.18f + 0.15f * Hh(ci, cj, 155);
            float k = bSm(rad, rad * 0.55f, d) * (0.5f + 0.5f * sinf(t * (0.5f + h) + h * 30.0f));
            Hsv(h * 2.0f + 0.5f, 0.9f, 1.0f, hr, hg, hb);
            float kk = k * (L ? 0.5f : 0.35f) * (h > 0.25f ? 1.0f : 0.0f);
            r += hr * kk; g += hg * kk; b += hb * kk;
        }
        float cr = 0.0f;
        for (int c = 0; c < 14; c++) {
            float h = Hh(c, 4, 161);
            float cx = (c + 0.5f + 0.3f * (h - 0.5f)) / 14.0f;
            float sp = 0.06f + 0.12f * Hh(c, 5, 161);
            float py = Fr(t * sp + h * 9.0f) * 1.3f - 0.1f;
            float wob = 0.004f * sinf(v * 40.0f + h * 30.0f);
            float dx = (u - cx - wob) * 1.0f;
            float head = bSm(0.012f + 0.006f * h, 0.002f, bLen(dx, (v - py) * 0.55f));
            float tr = bSm(0.004f, 0.0f, fabsf(dx)) * bSm(py - 0.25f, py, v) * (v < py ? 1.0f : 0.0f) * 0.35f;
            cr += head + tr;
        }
        float rf = Cl(cr);
        r += rf * 0.35f; g += rf * 0.4f; b += rf * 0.5f;
        float mist = bFbm(u * 6.0f, v * 6.0f - t * 0.1f) * 0.06f;
        r += mist; g += mist; b += mist * 1.5f;
        break;
    }
    case 11: {   // Dew spider web
        float bg = bFbm(u * 4.0f, v * 4.0f);
        r = 0.02f + 0.03f * bg; g = 0.05f + 0.07f * bg; b = 0.04f + 0.04f * bg;
        for (int i = 0; i < 4; i++) {
            float h = Hh(i, 8, 171);
            float k = xGl(bLen(u - Hh(i, 1, 172), v - Hh(i, 2, 172)), 40.0f) * (0.5f + 0.5f * sinf(t * 0.8f + h * 20.0f)) * 0.3f;
            Hsv(0.25f + 0.3f * h, 0.5f, 1.0f, hr, hg, hb);
            r += hr * k; g += hg * k; b += hb * k;
        }
        float rr = bLen(x * 1.0f, y * 1.0f), an = atan2f(y, x) + 0.04f * sinf(t * 0.8f + rr * 6.0f);
        float sd = fabsf(sinf(an * 6.0f)) * rr;
        float rg = fabsf(Fr(rr * 9.0f) - 0.5f) / 9.0f;
        float spoke = bSm(0.004f, 0.0f, sd) * bSm(0.55f, 0.5f, rr);
        float ring = bSm(0.0035f, 0.0f, rg) * bSm(0.55f, 0.5f, rr) * bSm(0.03f, 0.06f, rr);
        float line = bMax(spoke * 0.8f, ring * 0.9f);
        r += 0.75f * line; g += 0.8f * line; b += 0.85f * line;
        float dew = bSm(0.022f, 0.0f, bLen(sd * 1.0f, rg * 1.0f)) * bSm(0.5f, 0.45f, rr) * bSm(0.03f, 0.06f, rr);
        float sp = powf(0.5f + 0.5f * sinf(t * 2.0f + an * 6.0f + rr * 30.0f), 6.0f);
        r += dew * (0.6f + 0.8f * sp); g += dew * (0.8f + 0.6f * sp); b += dew * (0.9f + 0.4f * sp);
        break;
    }
    case 12: {   // Wolf howling at the moon
        ySky(v, 0.02f, 0.03f, 0.12f, 0.12f, 0.14f, 0.3f, r, g, b);
        xAddStars(r, g, b, xStar(u, v, 18.0f, 4, t) * 0.8f);
        float mc = yMoon(u, v, 0.62f, 0.3f, 0.17f, r, g, b);
        float cl = bFbm(u * 3.0f + t * 0.06f, v * 8.0f) * bSm(0.15f, 0.35f, v) * bSm(0.55f, 0.35f, v);
        r += cl * 0.08f; g += cl * 0.09f; b += cl * 0.15f;
        for (int i = 0; i < 3; i++) {
            float T = Fr(t * 0.35f + i / 3.0f);
            float d = bLen(u - 0.42f, v - 0.4f);
            float k = xGl(d - 0.05f - 0.25f * T, 1500.0f) * (1.0f - T) * 0.25f;
            r += k; g += k; b += k * 1.2f;
        }
        float hl = 0.7f - 0.04f * bSm(0.6f, 0.0f, fabsf(u - 0.28f)) - 0.015f * bFbm(u * 9.0f, 1.0f);
        float wd = bEll(u, v, 0.28f, 0.6f, 0.13f, 0.045f);
        wd = bMin(wd, bTap(u, v, 0.37f, 0.58f, 0.33f, 0.47f, 0.035f, 0.02f));
        wd = bMin(wd, bTap(u, v, 0.33f, 0.47f, 0.395f, 0.4f, 0.027f, 0.012f));
        wd = bMin(wd, bTap(u, v, 0.355f, 0.435f, 0.39f, 0.38f, 0.02f, 0.012f) * 1.0f);
        float ear = bMin(bTap(u, v, 0.335f, 0.46f, 0.325f, 0.42f, 0.012f, 0.0f), bTap(u, v, 0.35f, 0.455f, 0.36f, 0.41f, 0.011f, 0.0f));
        wd = bMin(wd, ear);
        wd = bMin(wd, bCap(u, v, 0.2f, 0.62f, 0.18f, 0.7f, 0.014f));
        wd = bMin(wd, bCap(u, v, 0.34f, 0.62f, 0.34f, 0.7f, 0.014f));
        wd = bMin(wd, bTap(u, v, 0.16f, 0.58f, 0.1f, 0.67f + 0.012f * sinf(t * 1.5f), 0.025f, 0.006f));
        bPut(r, g, b, 0.01f, 0.01f, 0.02f, bEdge(wd));
        if (v > hl) bPut(r, g, b, 0.01f, 0.015f, 0.025f, 1.0f);
        float tr = 0.0f;
        for (int i = 0; i < 6; i++) {
            float tx = 0.55f + 0.08f * i + 0.02f * Hh(i, 1, 181), th = 0.15f + 0.1f * Hh(i, 2, 181);
            float yy = 0.78f - v + th * 0.0f;
            float w = (0.045f + 0.02f * Hh(i, 3, 181)) * Cl((v - (0.8f - th * 2.0f)) / (th * 1.6f));
            if (v < 0.82f && v > 0.8f - th * 2.0f && fabsf(u - tx) < w) tr = 1.0f;
        }
        if (tr > 0.5f) bPut(r, g, b, 0.01f, 0.02f, 0.03f, 1.0f);
        float mist = bFbm(u * 5.0f + t * 0.08f, v * 8.0f) * bSm(0.72f, 0.95f, v) * 0.35f;
        r += mist * 0.4f; g += mist * 0.45f; b += mist * 0.6f;
        (void)mc;
        break;
    }
    case 13: {   // Hot air balloons
        ySky(v, 0.25f, 0.55f, 0.95f, 0.95f, 0.9f, 0.85f, r, g, b);
        float cl = bFbm(u * 4.0f + t * 0.05f, v * 6.0f);
        cl = bSm(0.5f, 0.75f, cl) * bSm(0.9f, 0.4f, v);
        r = bMix(r, 1.0f, cl * 0.8f); g = bMix(g, 1.0f, cl * 0.8f); b = bMix(b, 1.0f, cl * 0.8f);
        for (int i = 0; i < 3; i++) {
            float sc = 0.6f + 0.35f * i * 0.9f;
            float bx = 0.2f + 0.3f * i + 0.04f * sinf(t * 0.4f + i * 2.0f), by = 0.3f + 0.04f * i + 0.02f * sinf(t * 0.7f + i);
            float R = 0.12f * sc;
            float d = bEll(u, v, bx, by, R * 0.9f, R * 1.05f);
            float low = bTap(u, v, bx, by + R * 0.9f, bx, by + R * 1.45f, R * 0.5f, R * 0.18f);
            float env = bMin(d, low);
            float an = (u - bx) / (R * 0.9f);
            int st = (int)floorf((an * 0.5f + 0.5f) * 6.0f);
            float sh = 0.65f + 0.35f * Cl(1.0f - (an + 0.5f) * 0.6f);
            Hsv(Hh(i, st, 191) * 0.2f + (st & 1 ? 0.0f : 0.1f) + i * 0.3f, 0.8f, (st & 1) ? sh : sh * 0.95f, hr, hg, hb);
            float wh = (st & 1) ? 1.0f : 0.0f;
            bPut(r, g, b, bMix(hr, 1.0f * sh, wh * 0.0f), bMix(hg, 0.98f * sh, wh * 0.0f), bMix(hb, 0.95f * sh, wh * 0.0f), bEdge(env));
            float bk = xBox(u - bx, v - (by + R * 1.7f), R * 0.12f, R * 0.09f);
            bPut(r, g, b, 0.4f, 0.25f, 0.1f, bEdge(bk));
            float rp = bMin(bCap(u, v, bx - R * 0.35f, by + R * 1.3f, bx - R * 0.1f, by + R * 1.62f, 0.0015f), bCap(u, v, bx + R * 0.35f, by + R * 1.3f, bx + R * 0.1f, by + R * 1.62f, 0.0015f));
            bPut(r, g, b, 0.25f, 0.2f, 0.12f, bEdge(rp));
            float fl = xGl(bLen(u - bx, v - (by + R * 1.45f)), 2000.0f * 0.0f + 800.0f) * (0.6f + 0.4f * sinf(t * 25.0f + i));
            r += fl * 0.6f; g += fl * 0.4f;
        }
        break;
    }
    case 14: {   // Firefly forest
        ySky(v, 0.01f, 0.05f, 0.07f, 0.03f, 0.12f, 0.1f, r, g, b);
        for (int L = 0; L < 2; L++) {
            float n = L ? 5.0f : 8.0f;
            float uu = u * n + 0.31f * L + 0.04f * sinf(t * 0.2f);
            int ci = (int)floorf(uu);
            float cx = ci + 0.5f + 0.35f * (Hh(ci, L, 201) - 0.5f);
            float w = (L ? 0.1f : 0.06f) * (0.6f + 0.8f * Hh(ci, L, 202));
            float bend = 0.03f * sinf(v * 5.0f + ci);
            if (fabsf(uu - cx - bend) < w) {
                float c0 = L ? 0.015f : 0.04f;
                float bark = 0.5f + 0.5f * sinf(v * 60.0f + ci * 7.0f);
                bPut(r, g, b, c0, c0 + 0.015f * bark, c0 + 0.01f, 1.0f);
            }
            float fog = bFbm(u * 3.0f + t * 0.05f + L * 5.0f, v * 7.0f) * 0.12f * (1.0f - 0.4f * L);
            r += fog * 0.3f; g += fog * 0.6f; b += fog * 0.5f;
        }
        if (v > 0.9f) bPut(r, g, b, 0.01f, 0.03f, 0.02f, bSm(0.9f, 0.95f, v));
        for (int L = 0; L < 2; L++) {
            float n = L ? 9.0f : 6.0f;
            float su = u * n, sv = v * n;
            int ci = (int)floorf(su), cj = (int)floorf(sv);
            float h = Hh(ci, cj, 211 + L);
            float cx = ci + 0.5f + 0.35f * sinf(t * (0.4f + h) + h * 20.0f), cy = cj + 0.5f + 0.35f * cosf(t * (0.5f + h) + h * 11.0f);
            float bl = powf(0.5f + 0.5f * sinf(t * (1.0f + 2.0f * h) + h * 40.0f), 3.0f);
            float k = (h > 0.35f ? 1.0f : 0.0f) * bl * (xGl(bLen(su - cx, sv - cy), L ? 90.0f : 60.0f) * 1.4f);
            r += k * 0.75f; g += k; b += k * 0.2f;
        }
        break;
    }
    case 15: {   // Aurora lake
        float yy = v < 0.68f ? v : 1.36f - v + 0.012f * sinf(u * 50.0f + t * 2.0f + v * 20.0f);
        float uu = u;
        ySky(yy, 0.01f, 0.02f, 0.08f, 0.05f, 0.1f, 0.2f, r, g, b);
        xAddStars(r, g, b, xStar(uu, yy, 18.0f, 4, t) * 0.8f);
        float curtain = 0.0f;
        for (int k = 0; k < 2; k++) {
            float ph = uu * (3.0f + 2.0f * k) + sinf(uu * 5.0f + t * 0.5f + k) * 1.5f + t * 0.2f * (k + 1);
            float ray = 0.5f + 0.5f * sinf(ph * 4.0f + bFbm(uu * 8.0f + k, t * 0.3f) * 6.0f);
            float band = bSm(0.0f, 0.2f, yy) * bSm(0.7f, 0.3f, yy + 0.1f * sinf(uu * 4.0f + t * 0.4f + k));
            curtain += ray * band * (0.75f - 0.3f * k);
        }
        float h2 = 0.35f + 0.25f * sinf(uu * 3.0f + t * 0.3f);
        Hsv(0.33f + 0.3f * (1.0f - yy * 1.5f) + 0.1f * h2, 0.75f, 1.0f, hr, hg, hb);
        r += hr * curtain * 0.9f; g += hg * curtain * 0.9f; b += hb * curtain * 0.9f;
        float mt = 0.68f - 0.05f * bFbm(uu * 6.0f, 1.0f) - 0.09f * bSm(0.45f, 0.0f, fabsf(uu - 0.3f)) - 0.06f * bSm(0.35f, 0.0f, fabsf(uu - 0.8f));
        if (yy > mt && yy < 0.7f) bPut(r, g, b, 0.01f, 0.015f, 0.03f, 1.0f);
        if (v > 0.68f) { r *= 0.8f; g *= 0.85f; b *= 0.95f; }
        break;
    }
    case 16: {   // Tornado
        ySky(v, 0.12f, 0.15f, 0.14f, 0.35f, 0.4f, 0.3f, r, g, b);
        float cl = bFbm(u * 3.0f - t * 0.05f, v * 4.0f);
        r -= cl * 0.1f; g -= cl * 0.1f; b -= cl * 0.1f;
        float fl = Hh((int)(t * 4.0f), 3, 221) > 0.93f ? 1.0f : 0.0f;
        r += fl * 0.35f * bSm(0.5f, 0.0f, v); g += fl * 0.35f * bSm(0.5f, 0.0f, v); b += fl * 0.4f * bSm(0.5f, 0.0f, v);
        float gnd = 0.84f;
        float fh = Cl((gnd - v) / (gnd - 0.15f));
        float cx = 0.5f + 0.07f * sinf(v * 7.0f - t * 1.4f) * (1.0f - fh * 0.3f) + 0.06f * sinf(t * 0.3f);
        float hw = 0.025f + 0.22f * fh * fh + 0.01f;
        float dx = (u - cx) / hw;
        if (v < gnd + 0.02f && fabsf(dx) < 1.0f) {
            float sw = sinf(dx * 3.0f * (1.0f + fh) + v * 30.0f - t * 6.0f) * 0.5f + 0.5f;
            float tx = bFbm(u * 18.0f + t * 4.0f, v * 8.0f - t);
            float c = 0.15f + 0.3f * sw * tx + 0.2f * (1.0f - fabsf(dx));
            float e = bSm(1.0f, 0.8f, fabsf(dx));
            bPut(r, g, b, c * 0.9f, c, c * 0.85f, e * 0.95f);
        }
        float dust = bFbm(u * 6.0f + t, v * 12.0f) * bSm(gnd - 0.1f, gnd + 0.03f, v) * bSm(0.45f, 0.0f, fabsf(u - cx));
        r = bMix(r, 0.35f, dust * 0.6f); g = bMix(g, 0.3f, dust * 0.6f); b = bMix(b, 0.22f, dust * 0.6f);
        for (int i = 0; i < 8; i++) {
            float h = Hh(i, 9, 231);
            float a = t * (1.5f + h) + h * 20.0f, rr = (0.05f + 0.22f * h) * (0.3f + fh * 0.7f);
            float py = 0.3f + 0.5f * Hh(i, 2, 231);
            float fhh = Cl((gnd - py) / (gnd - 0.15f));
            float px = cx + (0.04f + 0.25f * fhh * fhh) * cosf(a);
            bPut(r, g, b, 0.05f, 0.04f, 0.03f, bSm(0.008f, 0.004f, bLen(u - px, v - py)) * (sinf(a) > -0.2f ? 1.0f : 0.3f));
            (void)rr;
        }
        if (v > gnd) bPut(r, g, b, 0.15f + 0.08f * bFbm(u * 10.0f, v * 30.0f), 0.17f + 0.08f * bFbm(u * 10.0f, v * 30.0f), 0.08f, 1.0f);
        break;
    }
    default: {   // 17 Snowy village at night
        ySky(v, 0.02f, 0.04f, 0.14f, 0.15f, 0.2f, 0.4f, r, g, b);
        xAddStars(r, g, b, xStar(u, v, 18.0f, 4, t) * 0.9f);
        yMoon(u, v, 0.22f, 0.18f, 0.07f, r, g, b);
        float h1 = 0.62f + 0.05f * sinf(u * 4.0f + 1.0f), h2 = 0.72f + 0.04f * sinf(u * 6.0f + 3.0f);
        if (v > h1) bPut(r, g, b, 0.45f, 0.52f, 0.7f, 1.0f);
        for (int i = 0; i < 3; i++) {
            float hx = 0.2f + 0.3f * i + 0.03f * Hh(i, 1, 241), hy = 0.62f + 0.04f * i * 0.0f + 0.05f * (i == 1 ? 1 : 0);
            float hw = 0.08f + 0.02f * Hh(i, 2, 241), hh = 0.07f;
            float bd = xBox(u - hx, v - hy, hw, hh * 0.5f);
            float rf = (v < hy - hh * 0.5f && v > hy - hh * 0.5f - hw * 0.8f) ? fabsf(u - hx) - hw * 1.15f * (v - (hy - hh * 0.5f - hw * 0.8f)) / (hw * 0.8f) : 1.0f;
            bPut(r, g, b, 0.15f, 0.08f, 0.06f, bEdge(bd));
            bPut(r, g, b, 0.9f, 0.92f, 1.0f, bEdge(rf));
            float fl = 0.8f + 0.2f * sinf(t * 4.0f + i * 3.0f);
            bPut(r, g, b, 1.0f * fl, 0.75f * fl, 0.3f * fl, bEdge(xBox(u - hx, v - hy, hw * 0.35f, hh * 0.22f)));
            float gl = xGl(bLen(u - hx, (v - hy) * 1.2f), 120.0f) * 0.25f;
            r += gl; g += gl * 0.7f; b += gl * 0.3f;
            float sm = bFbm(u * 14.0f + 3.0f * i, v * 14.0f - t * 1.5f) * bSm(0.07f, 0.0f, fabsf(u - hx - hw * 0.6f - 0.01f * (hy - v) * 4.0f)) * bSm(hy - hh * 0.5f - hw * 0.6f - 0.25f, hy - hh * 0.5f - hw * 0.6f, v) * (v < hy - hh * 0.5f - hw * 0.6f ? 1.0f : 0.0f);
            r += sm * 0.4f; g += sm * 0.4f; b += sm * 0.45f;
        }
        if (v > h2) bPut(r, g, b, 0.62f, 0.7f, 0.9f, 1.0f);
        for (int i = 0; i < 5; i++) {
            float tx = 0.08f + 0.2f * i + 0.04f * Hh(i, 3, 241), th = 0.12f + 0.05f * Hh(i, 4, 241), ty = 0.8f;
            float k = (v < ty && v > ty - th) ? fabsf(u - tx) - 0.035f * (v - (ty - th)) / th : 1.0f;
            bPut(r, g, b, 0.05f, 0.2f, 0.15f, bEdge(k));
        }
        for (int L = 0; L < 2; L++) {
            float n = 18.0f + 14.0f * L;
            float uu = u * n + 0.5f * sinf(t * 0.5f + v * 4.0f), vv = v * n + t * (1.5f + 1.5f * L) * 2.0f;
            int ci = (int)floorf(uu), cj = (int)floorf(vv);
            float h = Hh(ci, cj, 251 + L);
            if (h > 0.6f) {
                float k = bSm(0.17f - 0.05f * L, 0.05f, bLen(uu - ci - 0.5f, vv - cj - 0.5f));
                r += k * 0.9f; g += k * 0.9f; b += k;
            }
        }
        break;
    }
    }
}

// ---------------------------------------- SODA (21) ----------------------------------------
// 12 new flavours (same liquid + bubbles + foam look as the old ones) + 9 new drink scenes
static const SodaDef SODAS2[12] = {
    {{1.00f, 0.72f, 0.45f}, {0.92f, 0.38f, 0.18f}, {1.00f, 0.95f, 0.85f}, 1.1f, 0.6f},   // Peach
    {{1.00f, 0.92f, 0.35f}, {0.90f, 0.62f, 0.05f}, {1.00f, 1.00f, 0.85f}, 1.2f, 0.6f},   // Pineapple
    {{1.00f, 0.35f, 0.40f}, {0.55f, 0.04f, 0.12f}, {1.00f, 0.85f, 0.85f}, 1.1f, 0.5f},   // Watermelon
    {{0.96f, 1.00f, 0.90f}, {0.55f, 0.85f, 0.50f}, {1.00f, 1.00f, 1.00f}, 1.0f, 0.7f},   // Coconut lime
    {{0.95f, 0.78f, 0.35f}, {0.65f, 0.40f, 0.08f}, {1.00f, 0.96f, 0.82f}, 1.3f, 0.5f},   // Ginger ale
    {{0.82f, 0.95f, 1.00f}, {0.35f, 0.65f, 0.95f}, {1.00f, 1.00f, 1.00f}, 1.8f, 0.3f},   // Tonic water
    {{1.00f, 0.97f, 0.62f}, {0.95f, 0.82f, 0.22f}, {1.00f, 1.00f, 0.92f}, 0.8f, 0.6f},   // Lemonade
    {{1.00f, 0.55f, 0.50f}, {0.88f, 0.22f, 0.30f}, {1.00f, 0.90f, 0.88f}, 1.2f, 0.5f},   // Pink grapefruit
    {{0.35f, 0.30f, 0.85f}, {0.08f, 0.04f, 0.38f}, {0.85f, 0.82f, 1.00f}, 1.0f, 0.5f},   // Blueberry
    {{0.70f, 1.00f, 0.30f}, {0.20f, 0.65f, 0.05f}, {0.95f, 1.00f, 0.80f}, 1.3f, 0.5f},   // Green apple
    {{1.00f, 0.78f, 0.15f}, {0.95f, 0.42f, 0.02f}, {1.00f, 0.95f, 0.70f}, 1.1f, 0.6f},   // Mango
    {{0.28f, 0.08f, 0.22f}, {0.06f, 0.01f, 0.08f}, {0.95f, 0.80f, 0.95f}, 1.0f, 0.8f}    // Black currant
};
static void YSoda(int id, float u, float v, float t, float& r, float& g, float& b) {
    if (id < 12) { NSodaD(SODAS2[id], u, v, t, r, g, b); return; }
    float x = u - 0.5f, y = v - 0.5f;
    float hr, hg, hb;
    switch (id - 12) {
    case 0: {   // Layered rainbow soda
        const float L[6][3] = {{0.95f,0.15f,0.2f},{1.0f,0.55f,0.1f},{1.0f,0.9f,0.2f},{0.2f,0.8f,0.3f},{0.15f,0.55f,1.0f},{0.55f,0.2f,0.85f}};
        float w = 0.025f * sinf(u * 8.0f + t * 1.2f) + 0.015f * sinf(u * 15.0f - t * 1.8f);
        float f = Cl(v + w) * 6.0f;
        int k = (int)f; if (k > 5) k = 5;
        float fr = f - k;
        float mx = bSm(0.8f, 1.0f, fr);
        int k2 = k < 5 ? k + 1 : 5;
        r = bMix(L[k][0], L[k2][0], mx); g = bMix(L[k][1], L[k2][1], mx); b = bMix(L[k][2], L[k2][2], mx);
        float sh = 0.9f + 0.1f * sinf((u + v) * 14.0f - t * 2.0f);
        r *= sh; g *= sh; b *= sh;
        for (int i = 0; i < 14; i++) {
            float h = Hh(i, 1, 301);
            float bx = (i + 0.5f) / 14.0f + 0.015f * sinf(t * 2.0f + h * 20.0f);
            float by = 1.1f - Fr(t * (0.1f + 0.2f * h) + h) * 1.25f;
            float rad = 0.012f + 0.014f * Hh(i, 2, 301);
            float d = bLen(u - bx, v - by);
            float k3 = bSm(rad, rad * 0.5f, d) * 0.5f + bSm(rad * 0.2f, 0.0f, fabsf(d - rad * 0.8f)) * 0.5f;
            r = bMix(r, 1.0f, k3); g = bMix(g, 1.0f, k3); b = bMix(b, 1.0f, k3);
        }
        break;
    }
    case 1: {   // Pouring soda
        r = 0.08f + 0.08f * v; g = 0.05f + 0.05f * v; b = 0.04f + 0.04f * v;
        float lvl = 0.9f - 0.45f * Fr(t * 0.12f);
        float sw = 0.035f * sinf(u * 11.0f + t * 3.0f);
        if (v > lvl + sw * 0.5f) {
            float k = Cl((v - lvl) / 0.4f);
            r = bMix(0.45f, 0.1f, k); g = bMix(0.2f, 0.03f, k); b = bMix(0.06f, 0.01f, k);
            float fm = bSm(0.07f, 0.0f, v - lvl - sw * 0.5f);
            r = bMix(r, 1.0f, fm * 0.9f); g = bMix(g, 0.95f, fm * 0.9f); b = bMix(b, 0.85f, fm * 0.9f);
            float bub = Hh((int)(u * 36), (int)(v * 36 + t * 30.0f), 311) > 0.97f ? 0.5f : 0.0f;
            r += bub; g += bub * 0.9f; b += bub * 0.8f;
        }
        float sx = 0.5f + 0.015f * sinf(v * 20.0f - t * 6.0f), sw2 = 0.03f + 0.01f * sinf(v * 30.0f + t * 9.0f);
        if (v < lvl + 0.05f) {
            float k = bSm(sw2, sw2 * 0.4f, fabsf(u - sx));
            float st = 0.6f + 0.4f * sinf(v * 60.0f - t * 14.0f);
            r = bMix(r, 0.6f * st, k); g = bMix(g, 0.3f * st, k); b = bMix(b, 0.1f * st, k);
        }
        break;
    }
    case 2: {   // Ice cubes in cola
        r = 0.28f - 0.2f * v; g = 0.1f - 0.07f * v; b = 0.03f;
        r += 0.03f * sinf(u * 10.0f + t) ; g += 0.01f * sinf(u * 10.0f + t);
        for (int i = 0; i < 4; i++) {
            float h = Hh(i, 3, 321);
            float cx = 0.2f + 0.2f * i + 0.04f * sinf(t * 0.6f + i * 2.0f), cy = 0.3f + 0.45f * Hh(i, 4, 321) + 0.04f * sinf(t * 0.8f + i);
            float px = u - cx, py = v - cy;
            yRot(px, py, 0.4f * sinf(t * 0.5f + i * 3.0f) + h);
            float d = xBox(px, py, 0.11f, 0.1f) - 0.015f;
            float e = bEdge(d);
            float sh = 0.6f + 0.4f * Cl(0.5f - px * 3.0f - py * 2.0f);
            bPut(r, g, b, 0.75f * sh, 0.9f * sh, 1.0f * sh, e * 0.55f);
            bPut(r, g, b, 0.95f, 1.0f, 1.0f, bSm(0.012f, 0.0f, fabsf(d + 0.02f)) * 0.35f * e);
        }
        for (int i = 0; i < 10; i++) {
            float h = Hh(i, 5, 321);
            float bx = (i + 0.5f) / 10.0f, by = 1.1f - Fr(t * (0.12f + 0.2f * h) + h) * 1.25f;
            float k = bSm(0.015f, 0.006f, bLen(u - bx - 0.02f * sinf(t * 2 + h * 9), v - by));
            r += k * 0.6f; g += k * 0.5f; b += k * 0.4f;
        }
        float fm = bSm(0.07f, 0.0f, v);
        r = bMix(r, 0.95f, fm * 0.8f); g = bMix(g, 0.85f, fm * 0.8f); b = bMix(b, 0.7f, fm * 0.8f);
        break;
    }
    case 3: {   // Fizz close-up
        float k0 = 0.5f + 0.5f * sinf(v * 3.0f + t * 0.4f);
        r = 0.9f * bMix(0.9f, 0.6f, v); g = bMix(0.75f, 0.45f, v); b = bMix(0.25f, 0.1f, v);
        for (int L = 0; L < 3; L++) {
            float n = 5.0f + 4.0f * L;
            float su = u * n, sv = v * n + t * (0.8f + 0.5f * L);
            int ci = (int)floorf(su), cj = (int)floorf(sv);
            float h = Hh(ci, cj, 331 + L);
            if (h > 0.4f) {
                float cx = ci + 0.3f + 0.4f * Hh(ci, cj, 335), cy = cj + 0.3f + 0.4f * Hh(ci, cj, 336) + 0.1f * sinf(t * 2.0f + h * 20.0f);
                float rad = 0.17f + 0.13f * h;
                float d = bLen(su - cx, sv - cy);
                float body = bSm(rad, rad * 0.8f, d) * 0.28f;
                float rim = bSm(rad * 0.18f, 0.0f, fabsf(d - rad * 0.9f)) * 0.85f;
                float hl = bSm(rad * 0.3f, 0.0f, bLen(su - cx + rad * 0.4f, sv - cy + rad * 0.4f)) * 0.9f;
                float a = Cl(body + rim + hl);
                r = bMix(r, 1.0f, a); g = bMix(g, 1.0f, a); b = bMix(b, 0.95f, a);
            }
        }
        r *= 0.85f + 0.15f * k0;
        break;
    }
    case 4: {   // Straw swirl
        float an = atan2f(y, x), d = bLen(x, y);
        float tw = an * 2.0f + d * 14.0f - t * 2.0f;
        float s = sinf(tw);
        float m = bSm(-0.2f, 0.2f, s);
        r = bMix(0.95f, 1.0f, m); g = bMix(0.1f, 0.97f, m); b = bMix(0.15f, 0.97f, m);
        float sh = 0.75f + 0.25f * cosf(an - t * 0.6f);
        r *= sh; g *= sh; b *= sh;
        float inner = bSm(0.04f, 0.0f, d);
        r = bMix(r, 0.1f, inner); g = bMix(g, 0.05f, inner); b = bMix(b, 0.05f, inner);
        break;
    }
    case 5: {   // Cold can with condensation
        r = 0.55f + 0.2f * sinf(u * 5.0f); g = 0.7f + 0.15f * sinf(u * 5.0f); b = 0.85f + 0.1f * sinf(u * 5.0f);
        float band = bSm(0.04f, 0.0f, fabsf(v - 0.35f)) + bSm(0.04f, 0.0f, fabsf(v - 0.65f));
        r = bMix(r, 0.9f, band * 0.5f); g = bMix(g, 0.1f, band * 0.5f); b = bMix(b, 0.15f, band * 0.5f);
        float stp = bSm(0.09f, 0.0f, fabsf(v - 0.5f)) * 0.9f;
        r = bMix(r, 0.95f, stp); g = bMix(g, 0.12f, stp); b = bMix(b, 0.12f, stp);
        float sh = 0.8f + 0.2f * sinf(u * 20.0f);
        r *= sh; g *= sh; b *= sh;
        for (int L = 0; L < 2; L++) {
            float n = L ? 14.0f : 8.0f;
            float su = u * n, sv = v * n * 0.8f;
            int ci = (int)floorf(su), cj = (int)floorf(sv);
            float h = Hh(ci, cj, 341 + L);
            float ph = Fr(t * (0.03f + 0.04f * h) + h * 5.0f);
            float cx = ci + 0.5f + 0.2f * (Hh(ci, cj, 345) - 0.5f);
            float cy = cj + 0.5f + (ph - 0.5f) * 0.0f;
            float dx = su - cx, dy = sv - cy;
            float slide = (h > 0.7f) ? ph * 1.0f : 0.0f;
            float d = bLen(dx * 1.0f, (dy - slide + 0.5f * (h > 0.7f ? 0.0f : 0.0f)) * 0.8f);
            float rad = 0.12f + 0.12f * h;
            float k = bSm(rad, rad * 0.6f, d);
            float hl = bSm(rad * 0.35f, 0.0f, bLen(dx + rad * 0.3f, dy - slide + rad * 0.3f));
            r = bMix(r, 0.85f, k * 0.35f); g = bMix(g, 0.95f, k * 0.35f); b = bMix(b, 1.0f, k * 0.35f);
            r += hl * 0.5f; g += hl * 0.5f; b += hl * 0.5f;
        }
        break;
    }
    case 6: {   // Float (ice cream + cola)
        float w = 0.03f * sinf(u * 9.0f + t * 1.5f);
        float cola = Cl(v + w);
        r = bMix(0.3f, 0.06f, cola); g = bMix(0.12f, 0.02f, cola); b = bMix(0.04f, 0.01f, cola);
        float fx = u + 0.04f * sinf(v * 10.0f + t), fy = v + 0.03f * sinf(u * 8.0f - t * 0.8f);
        float sc = bEll(fx, fy, 0.5f, 0.4f, 0.28f, 0.2f);
        float sc2 = bEll(fx, fy, 0.25f, 0.6f, 0.18f, 0.14f);
        float sc3 = bEll(fx, fy, 0.78f, 0.62f, 0.16f, 0.13f);
        float sd = bMin(sc, bMin(sc2, sc3));
        float lit = 0.8f + 0.2f * cosf((fx - 0.5f) * 5.0f - (fy - 0.4f) * 3.0f);
        float ctr = 0.5f + 0.5f * sinf(fx * 30.0f + fy * 10.0f);
        bPut(r, g, b, 1.0f * lit, 0.95f * lit - 0.04f * ctr, 0.8f * lit - 0.06f * ctr, bEdge(sd));
        float fm = bSm(0.08f, 0.0f, v - 0.0f) ;
        r = bMix(r, 0.98f, fm * 0.7f); g = bMix(g, 0.92f, fm * 0.7f); b = bMix(b, 0.8f, fm * 0.7f);
        for (int i = 0; i < 8; i++) {
            float h = Hh(i, 6, 351);
            float bx = (i + 0.5f) / 8.0f, by = 1.1f - Fr(t * (0.1f + 0.2f * h) + h) * 1.25f;
            float k = bSm(0.013f, 0.005f, bLen(u - bx, v - by));
            r += k * 0.5f; g += k * 0.45f; b += k * 0.4f;
        }
        break;
    }
    case 7: {   // Slushie swirl
        float an = atan2f(y, x), d = bLen(x, y);
        float tw = an * 3.0f + d * 8.0f - t * 1.2f;
        float m = 0.5f + 0.5f * sinf(tw);
        float cr = 0.5f + 0.5f * sinf(an * 2.0f + d * 5.0f - t * 0.8f + 1.0f);
        r = bMix(0.95f, 0.2f, m * cr); g = bMix(0.2f, 0.55f, m); b = bMix(0.5f, 1.0f, m);
        float ice = bFbm(u * 30.0f, v * 30.0f + t * 0.2f);
        r = bMix(r, 1.0f, bSm(0.6f, 0.85f, ice) * 0.6f); g = bMix(g, 1.0f, bSm(0.6f, 0.85f, ice) * 0.6f); b = bMix(b, 1.0f, bSm(0.6f, 0.85f, ice) * 0.6f);
        float sp = Hh((int)(u * 70), (int)(v * 70), (int)(t * 5)) > 0.985f ? 1.0f : 0.0f;
        r += sp; g += sp; b += sp;
        break;
    }
    default: {   // 8 Fizzy geyser
        r = 0.08f + 0.1f * (1.0f - v); g = 0.12f + 0.12f * (1.0f - v); b = 0.2f + 0.2f * (1.0f - v);
        float T = Fr(t * 0.25f);
        float ht = 0.85f - 0.8f * powf(T, 0.5f) * (1.0f - 0.5f * T);
        float cx = 0.5f + 0.015f * sinf(t * 8.0f);
        float w = 0.05f + 0.1f * (ht - v < 0.0f ? 0.0f : 0.0f);
        float col = 0.0f;
        for (int i = 0; i < 10; i++) {
            float h = Hh(i, 7, 361);
            float py = 0.9f - Fr(t * (0.5f + 0.5f * h) + h) * 0.9f;
            float spread = (0.04f + 0.3f * (0.9f - py)) * (h - 0.5f) * 2.0f;
            float px = cx + spread * 0.5f;
            col += bSm(0.07f + 0.04f * h, 0.02f, bLen(u - px, v - py)) * 0.7f;
        }
        float jet = bSm(0.05f + 0.1f * (0.9f - v), 0.0f, fabsf(u - cx)) * bSm(0.0f, 0.1f, v) * (v > ht - 0.0f ? 1.0f : 0.0f);
        float c = Cl(col * 0.6f + jet * 0.8f);
        float fz = bFbm(u * 14.0f, v * 14.0f - t * 3.0f);
        c = Cl(c * (0.7f + 0.5f * fz));
        r = bMix(r, 0.35f, c); g = bMix(g, 0.18f, c); b = bMix(b, 0.07f, c);
        float fm = bSm(0.5f, 0.9f, c) * 0.9f;
        r = bMix(r, 0.97f, fm); g = bMix(g, 0.93f, fm); b = bMix(b, 0.85f, fm);
        if (v > 0.9f) { bPut(r, g, b, 0.15f, 0.1f, 0.08f, bSm(0.9f, 0.92f, v)); bPut(r, g, b, 0.1f, 0.7f, 0.3f, bEdge(xBox(u - cx, v - 0.95f, 0.04f, 0.04f))); }
        (void)hr; (void)hg; (void)hb;
        break;
    }
    }
}

// ids 261..321
static void XV11(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.0f;
    if (id < X_SCENE0) YParty(id - X_PARTY0, u, v, t, r, g, b);
    else if (id < X_SODA0) YScene(id - X_SCENE0, u, v, t, r, g, b);
    else YSoda(id - X_SODA0, u, v, t, r, g, b);
}

// ======================= v1.2: ANIMALS / BRANDS / FOOD&FUN (62 new, ids 322..383; drawn at 128x128 and doubled) =======================
// Animals 322-340 (19) | Brands 341-361 (21) | Food&Fun 362-383 (22)
// -> Animals, Brands and Food&Fun now have 32 designs each = at least 4 full pages in the menu.
static const int X_ANIMAL12 = 322, X_BRAND12 = 341, X_FUN12 = 362, X_V12_END = 384;

// ---------------------------------------- ANIMALS (19 new, ids 322..340) ----------------------------------------
static void ZAnimal(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.02f;
    switch (id) {
    case 0: {   // Black panther: ghost rosettes + glowing eyes
        float fill, inner, h; nSpots(u, v, 7.0f, t, 0.06f, 0.2f, 0.2f, 0.32f, fill, inner, h);
        float fur = 0.9f + 0.1f * Hh((int)(u * 170), (int)(v * 170), 6);
        float ring = Cl(fill - inner);
        float base = 0.035f * fur, sh = 0.5f + 0.5f * sinf(u * 9.0f + v * 5.0f - t * 0.6f);
        r = base + 0.05f * ring + 0.02f * sh; g = base + 0.055f * ring + 0.025f * sh; b = base * 1.2f + 0.07f * ring + 0.04f * sh;
        float bl = 1.0f - bSm(0.92f, 0.99f, sinf(t * 1.1f));
        for (int k = 0; k < 2; k++) {
            float ex = (k ? 0.7f : 0.3f) + 0.02f * sinf(t * 0.4f), ey = 0.46f + 0.015f * sinf(t * 0.3f);
            float e = bEll(u, v, ex, ey, 0.10f, 0.045f * bl + 0.004f);
            float glow = xGl(bLen(u - ex, (v - ey) * 2.0f), 120.0f) * 0.45f;
            r += 0.4f * glow; g += 0.9f * glow; b += 0.1f * glow;
            bPut(r, g, b, 0.55f, 1.0f, 0.15f, bEdge(e));
            bPut(r, g, b, 0.02f, 0.03f, 0.0f, bSm(0.012f, 0.0f, fabsf(u - ex)) * bEdge(e));
        }
        break;
    }
    case 1: {   // Snow leopard
        float fill, inner, h; nSpots(u, v, 6.0f, t, 0.08f, 0.05f, 0.22f, 0.34f, fill, inner, h);
        float fur = 0.9f + 0.1f * Hh((int)(u * 170), (int)(v * 170), 7);
        float n = bFbm(u * 4.0f + t * 0.04f, v * 4.0f);
        r = bMix(0.88f, 0.70f, n) * fur; g = bMix(0.90f, 0.73f, n) * fur; b = bMix(0.94f, 0.80f, n) * fur;
        float ring = Cl(fill - inner);
        r = bMix(r, 0.16f, ring * 0.95f); g = bMix(g, 0.17f, ring * 0.95f); b = bMix(b, 0.20f, ring * 0.95f);
        r = bMix(r, 0.55f, inner * 0.3f); g = bMix(g, 0.56f, inner * 0.3f); b = bMix(b, 0.60f, inner * 0.3f);
        float f2, i2, h2; nSpots(u + 0.3f, v + 0.2f, 14.0f, t, 0.1f, 0.4f, 0.10f, 0.20f, f2, i2, h2);
        r = bMix(r, 0.30f, f2 * 0.7f); g = bMix(g, 0.31f, f2 * 0.7f); b = bMix(b, 0.34f, f2 * 0.7f);
        break;
    }
    case 2: {   // White tiger
        float n = bFbm(u * 3.0f + t * 0.05f, v * 3.0f);
        float w = u * 8.0f + n * 3.2f + 0.5f * sinf(v * 3.0f + t * 0.6f) + t * 0.12f;
        float stripe = bSm(0.15f, 0.05f, fabsf(Fr(w) - 0.5f));
        float fur = 0.88f + 0.12f * Hh((int)(u * 180), (int)(v * 180), 8);
        float cool = 0.04f * sinf(v * 6.0f + t);
        r = bMix(0.95f * fur - cool, 0.04f, stripe); g = bMix(0.96f * fur, 0.05f, stripe); b = bMix(1.0f * fur + cool, 0.08f, stripe);
        break;
    }
    case 3: {   // Jaguar rosettes with centre dots
        float x = u * 5.0f + t * 0.06f, y = v * 5.0f;
        int ix = (int)floorf(x), iy = (int)floorf(y);
        float fx = Fr(x) - 0.5f - (Hh(ix, iy, 32) - 0.5f) * 0.3f, fy = Fr(y) - 0.5f - (Hh(ix, iy, 33) - 0.5f) * 0.3f;
        float d = bLen(fx, fy), R = 0.26f + 0.08f * Hh(ix, iy, 34);
        float on = Hh(ix, iy, 31) > 0.12f ? 1.0f : 0.0f;
        float fur = 0.9f + 0.1f * Hh((int)(u * 170), (int)(v * 170), 9);
        float ring = bSm(R, R - 0.05f, d) * bSm(R * 0.62f, R * 0.62f + 0.05f, d) * on;
        float dot = bSm(0.07f, 0.04f, d) * on;
        float inside = bSm(R * 0.62f, R * 0.62f - 0.04f, d) * on;
        r = 0.95f * fur; g = 0.62f * fur; b = 0.16f * fur;
        r = bMix(r, 0.80f * fur, inside); g = bMix(g, 0.50f * fur, inside); b = bMix(b, 0.10f * fur, inside);
        r = bMix(r, 0.08f, ring); g = bMix(g, 0.04f, ring); b = bMix(b, 0.01f, ring);
        r = bMix(r, 0.06f, dot); g = bMix(g, 0.03f, dot); b = bMix(b, 0.01f, dot);
        break;
    }
    case 4: {   // Lion mane: flowing radial strands
        float x = u - 0.5f, y = v - 0.5f, rr = bLen(x, y), ang = atan2f(y, x);
        float s = 0.5f + 0.5f * sinf(ang * 28.0f + 1.6f * sinf(rr * 11.0f - t * 1.0f));
        int sec = (int)floorf((ang + 3.14159f) / kTau * 56.0f);
        float h = Hh(sec, 0, 5);
        float k = Cl(rr * 1.6f + s * 0.35f + h * 0.25f);
        r = bMix(0.22f, 1.0f, k); g = bMix(0.09f, 0.68f, k); b = bMix(0.02f, 0.18f, k);
        float hl = powf(0.5f + 0.5f * sinf(ang * 3.0f - t * 0.9f), 6.0f) * 0.25f * s;
        r += hl; g += hl * 0.8f; b += hl * 0.4f;
        break;
    }
    case 5: {   // Flamingo feathers
        float rows = 9.0f, y = v * rows;
        int iy = (int)floorf(y);
        float fy = Fr(y), x = u * 7.0f + (iy & 1) * 0.5f + 0.2f * sinf(t * 0.8f + iy);
        float fx = Fr(x) - 0.5f;
        float sd = bLen(fx * 1.0f, (fy - 0.15f) * 0.9f);
        float inside = bSm(0.5f, 0.45f, sd);
        float barb = 0.9f + 0.1f * sinf(fx * 40.0f + sinf(fy * 6.0f + t) * 2.0f);
        float k = Cl(fy * 0.9f + 0.1f * Hh((int)floorf(x), iy, 4));
        float cr = bMix(1.00f, 1.00f, k), cg = bMix(0.35f, 0.62f, k), cb = bMix(0.50f, 0.70f, k);
        r = bMix(0.55f, cr * barb, inside); g = bMix(0.10f, cg * barb, inside); b = bMix(0.22f, cb * barb, inside);
        float edge = bSm(0.46f, 0.5f, sd) * inside;
        r = bMix(r, 0.85f, edge * 0.5f); g = bMix(g, 0.25f, edge * 0.5f); b = bMix(b, 0.40f, edge * 0.5f);
        break;
    }
    case 6: {   // Chameleon skin: colour-shifting cells
        float f1, f2, hid; nVor(u * 8.0f, v * 8.0f, t, 0.8f, f1, f2, hid);
        float hue = hid * 0.4f + 0.25f + 0.15f * sinf(t * 0.5f + u * 3.0f) + 0.2f * bFbm(u * 3.0f + t * 0.1f, v * 3.0f);
        float hr, hg, hb; Hsv(hue, 0.8f, 0.95f - 0.35f * f1, hr, hg, hb);
        float wall = 0.35f + 0.65f * bSm(0.0f, 0.12f, f2 - f1);
        float sp = Hh((int)(u * 120), (int)(v * 120), 5) > 0.93f ? 0.2f : 0.0f;
        r = hr * wall + sp; g = hg * wall + sp; b = hb * wall + sp;
        break;
    }
    case 7: {   // Poison dart frog: blue skin, black blotches, wet glints
        float fill, inner, h; nSpots(u, v, 5.0f, t, 0.05f, 0.15f, 0.22f, 0.40f, fill, inner, h);
        float f2, i2, h2; nSpots(u + 0.37f, v + 0.11f, 11.0f, t, 0.07f, 0.35f, 0.12f, 0.22f, f2, i2, h2);
        float n = bFbm(u * 6.0f, v * 6.0f - t * 0.1f);
        r = 0.0f + 0.05f * n; g = 0.30f + 0.20f * n; b = 0.95f - 0.15f * n;
        float bl = bMax(fill, f2);
        r = bMix(r, 0.01f, bl); g = bMix(g, 0.01f, bl); b = bMix(b, 0.03f, bl);
        float gl = powf(0.5f + 0.5f * sinf((u * 1.3f + v) * 7.0f - t * 1.2f), 10.0f) * 0.45f;
        r += gl; g += gl; b += gl;
        break;
    }
    case 8: {   // Clownfish bands
        float w = u * 3.0f + 0.12f * sinf(v * 5.0f + t * 1.2f) + t * 0.1f, f = Fr(w);
        float outl = nBar(f, 0.34f, 0.66f), band = nBar(f, 0.40f, 0.60f);
        float shim = 0.92f + 0.08f * sinf((u + v) * 40.0f - t * 3.0f);
        r = 1.0f * shim; g = 0.45f * shim; b = 0.04f;
        r = bMix(r, 0.03f, outl); g = bMix(g, 0.03f, outl); b = bMix(b, 0.03f, outl);
        r = bMix(r, 0.98f * shim, band); g = bMix(g, 0.98f * shim, band); b = bMix(b, 0.98f * shim, band);
        break;
    }
    case 9: {   // Betta fins
        float rr = bLen(u - 0.5f, v - 1.1f), ang = atan2f(u - 0.5f, -(v - 1.1f));
        float ray = 0.5f + 0.5f * sinf(ang * 38.0f + 2.5f * sinf(rr * 8.0f - t * 1.2f));
        float hr, hg, hb; Hsv(0.62f + 0.25f * rr + 0.05f * sinf(t), 0.85f, 0.25f + 0.75f * ray * (1.0f - rr * 0.5f), hr, hg, hb);
        float mem = 0.5f + 0.5f * sinf(rr * 14.0f - t * 1.5f);
        r = hr + 0.06f * mem; g = hg; b = hb + 0.08f * mem;
        break;
    }
    case 10: {  // Octopus skin
        float f1, f2, hid; nVor(u * 9.0f, v * 9.0f, t, 1.5f, f1, f2, hid);
        float hue = 0.95f + 0.25f * bFbm(u * 3.0f + t * 0.15f, v * 3.0f - t * 0.1f) + 0.1f * hid;
        float hr, hg, hb; Hsv(hue, 0.75f, 0.35f + 0.65f * Cl(1.0f - f1 * 1.3f), hr, hg, hb);
        float sp = bSm(0.18f, 0.0f, f1) * 0.35f;
        r = hr + sp; g = hg + sp; b = hb + sp;
        break;
    }
    case 11: {  // Crocodile skin
        float y = v * 10.0f; int iy = (int)floorf(y);
        float x = u * 8.0f + (iy & 1) * 0.5f; int ix = (int)floorf(x);
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f;
        float e = bMin(0.5f - fabsf(fx), 0.5f - fabsf(fy));
        float cell = bSm(0.03f, 0.12f, e), h = Hh(ix, iy, 7);
        float keel = bSm(0.12f, 0.0f, fabsf(fx));
        float sweep = 0.5f + 0.5f * sinf((u + v) * 5.0f - t * 1.2f);
        float k = (0.55f + 0.45f * sweep) * cell;
        r = (0.16f + 0.12f * h + 0.08f * keel) * k + 0.01f; g = (0.30f + 0.10f * h + 0.08f * keel) * k + 0.01f; b = (0.07f + 0.03f * h) * k;
        break;
    }
    case 12: {  // Owl feathers
        float y = v * 8.0f; int iy = (int)floorf(y);
        float fy = Fr(y), x = u * 6.0f + (iy & 1) * 0.5f + 0.15f * sinf(t * 0.7f + iy * 1.3f);
        int ix = (int)floorf(x); float fx = Fr(x) - 0.5f;
        float sd = bLen(fx, (fy - 0.1f) * 0.85f), inside = bSm(0.5f, 0.46f, sd);
        float h = Hh(ix, iy, 12);
        float bar = 0.5f + 0.5f * sinf(fy * 22.0f);
        float k = 0.55f + 0.25f * h + 0.2f * bar;
        float spot = bSm(0.09f, 0.06f, bLen(fx, fy - 0.55f)) * (h > 0.5f ? 1.0f : 0.0f);
        r = bMix(0.12f, 0.55f * k, inside); g = bMix(0.07f, 0.38f * k, inside); b = bMix(0.04f, 0.20f * k, inside);
        r = bMix(r, 0.95f, spot * inside); g = bMix(g, 0.88f, spot * inside); b = bMix(b, 0.72f, spot * inside);
        break;
    }
    case 13: {  // Ladybugs on a leaf
        float x = u * 3.0f, y = v * 3.0f; int ix = (int)floorf(x), iy = (int)floorf(y);
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f;
        float h = Hh(ix, iy, 13);
        fy += 0.02f * sinf(t * 2.0f + h * 20.0f); fx += 0.03f * sinf(t * 3.0f + h * 31.0f);
        r = 0.08f + 0.04f * v; g = 0.38f + 0.12f * bFbm(u * 8.0f, v * 8.0f); b = 0.08f;
        float sh = bEll(fx, fy, 0.0f, 0.03f, 0.36f, 0.40f);
        float head = bEll(fx, fy, 0.0f, -0.34f, 0.16f, 0.09f);
        float gap = 0.006f + 0.02f * (0.5f + 0.5f * sinf(t * 2.5f + h * 9.0f));
        float lit = 0.75f + 0.25f * Cl(1.0f - bLen((fx + 0.1f) * 3.0f, (fy + 0.12f) * 3.0f));
        bPut(r, g, b, 0.03f, 0.03f, 0.03f, bEdge(sh - 0.012f));
        bPut(r, g, b, 0.9f * lit, 0.05f * lit, 0.06f * lit, bEdge(sh));
        float sp = 0.0f;
        const float SX[6] = {-0.18f, 0.18f, -0.22f, 0.22f, -0.10f, 0.10f}, SY[6] = {-0.12f, -0.12f, 0.08f, 0.08f, 0.24f, 0.24f};
        for (int i = 0; i < 6; i++) sp = bMax(sp, bEdge(bLen(fx - SX[i], fy - SY[i]) - 0.055f));
        bPut(r, g, b, 0.03f, 0.03f, 0.03f, sp * bEdge(sh));
        bPut(r, g, b, 0.02f, 0.02f, 0.02f, bSm(gap, 0.0f, fabsf(fx)) * bEdge(sh));
        bPut(r, g, b, 0.03f, 0.03f, 0.03f, bEdge(head));
        break;
    }
    case 14: {  // Dragonfly wing: veins + iridescent membrane
        float f1, f2, hid; nVor(u * 7.0f, v * 5.0f, t, 0.3f, f1, f2, hid);
        float vein = bSm(0.10f, 0.0f, f2 - f1);
        float sheen = 0.5f + 0.5f * sinf((u * 1.2f + v) * 5.0f - t * 1.2f);
        float hr, hg, hb; Hsv(0.45f + 0.35f * sheen + 0.1f * hid, 0.65f, 0.15f + 0.55f * sheen * sheen, hr, hg, hb);
        float major = bSm(0.02f, 0.0f, xEdge(v * 4.0f + 0.1f * sinf(u * 5.0f)));
        float glint = powf(0.5f + 0.5f * sinf((u - v) * 7.0f - t * 2.0f), 12.0f) * 0.4f;
        r = bMix(hr, 0.95f, vein * 0.9f); g = bMix(hg, 0.78f, vein * 0.9f); b = bMix(hb, 0.25f, vein * 0.9f);
        r = bMix(r, 0.95f, major); g = bMix(g, 0.8f, major); b = bMix(b, 0.3f, major);
        r += glint; g += glint; b += glint;
        break;
    }
    case 15: {  // Bat swarm over the moon
        r = 0.05f + 0.1f * v; g = 0.02f + 0.04f * v; b = 0.18f + 0.15f * v;
        float md = bLen(u - 0.72f, v - 0.28f);
        float moon = bSm(0.17f, 0.15f, md);
        bPut(r, g, b, 0.97f, 0.93f, 0.7f, moon);
        r += 0.35f * xGl(md, 14.0f); g += 0.3f * xGl(md, 14.0f); b += 0.15f * xGl(md, 14.0f);
        float bat = 0.0f;
        for (int i = 0; i < 6; i++) {
            float h = Hh(i, 2, 15), s = 0.7f + 0.8f * Hh(i, 3, 15);
            float bx = Fr(t * (0.04f + 0.05f * h) + h * 5.0f) * 1.4f - 0.2f;
            float by = 0.15f + 0.7f * Hh(i, 4, 15) + 0.05f * sinf(t * 2.0f + i);
            float fl = sinf(t * 9.0f + h * 20.0f);
            float px = u - bx, py = v - by;
            float bd = bEll(px, py, 0.0f, 0.0f, 0.018f * s, 0.03f * s);
            for (int k = -1; k <= 1; k += 2) {
                float wx = k * 0.09f * s, wy = -0.045f * s * fl - 0.01f * s;
                bd = bMin(bd, bTap(px, py, k * 0.01f, 0.0f, wx, wy, 0.012f * s, 0.003f * s));
                bd = bMin(bd, bTap(px, py, wx, wy, k * 0.05f * s, 0.03f * s, 0.004f * s, 0.004f * s));
            }
            bat = bMax(bat, bEdge(bd));
        }
        bPut(r, g, b, 0.01f, 0.01f, 0.02f, bat);
        break;
    }
    case 16: {  // Sea turtle shell
        float hid; float e = nHex(u * 4.5f, v * 4.5f, hid);
        float ring = 0.5f + 0.5f * sinf(e * 38.0f), seam = bSm(0.07f, 0.02f, e);
        float c = bFbm(u * 6.0f + t * 0.3f, v * 6.0f - t * 0.2f);
        float k = 0.55f + 0.45f * ring;
        r = (0.30f + 0.28f * hid) * k; g = (0.24f + 0.16f * hid) * k; b = (0.07f + 0.03f * hid) * k;
        float ca = powf(c, 3.0f) * 0.9f;
        r += ca * 0.35f; g += ca * 0.45f; b += ca * 0.35f;
        r = bMix(r, 0.03f, seam); g = bMix(g, 0.04f, seam); b = bMix(b, 0.02f, seam);
        break;
    }
    case 17: {  // Fox fur: orange strands, white tips
        float flow = bFbm(u * 5.0f + t * 0.1f, v * 3.0f) * 18.0f;
        float st = 0.5f + 0.5f * sinf(u * 140.0f + flow + sinf(v * 5.0f + t * 0.8f) * 3.0f);
        float n = bVn(u * 120.0f, v * 10.0f + flow * 0.1f);
        float k = Cl(v * 1.1f + 0.25f * (st - 0.5f) + 0.15f * (n - 0.5f) + 0.1f * sinf(u * 3.0f + t * 0.5f));
        float tip = bSm(0.55f, 0.95f, k);
        r = bMix(0.95f, 1.0f, tip) * (0.75f + 0.25f * st); g = bMix(0.42f, 0.97f, tip) * (0.75f + 0.25f * st); b = bMix(0.08f, 0.93f, tip) * (0.75f + 0.25f * st);
        break;
    }
    default: {  // 18 Hummingbird iridescence
        float n = bFbm(u * 3.0f, v * 3.0f);
        float hue = 0.35f + 0.35f * sinf(u * 3.0f + v * 2.0f + t * 0.7f + n * 3.0f);
        float barb = 0.6f + 0.4f * sinf((u * 0.8f + v) * 90.0f + n * 6.0f);
        float scale = 0.65f + 0.35f * sinf(u * 28.0f) * sinf(v * 28.0f + 1.0f);
        float hr, hg, hb; Hsv(hue, 0.85f, Cl(0.25f + 0.55f * barb * scale), hr, hg, hb);
        float gl = powf(0.5f + 0.5f * sinf(u * 4.0f - v * 2.0f - t * 1.1f), 8.0f) * 0.35f;
        r = hr + gl; g = hg + gl; b = hb + gl;
        break;
    }
    }
}

// ---------------------------------------- BRANDS (21 new, ids 341..361; colours + patterns only, no logos) ----------------------------------------
// bands: colour c[i] covers [e[i-1], e[i]) of the repeating value f; soft edges
static NRgb zBand(float f, const NRgb* c, const float* e, int n) {
    f = Fr(f);
    NRgb o = c[0];
    for (int i = 1; i < n; i++) o = nMix(o, c[i], bSm(e[i - 1] - 0.006f, e[i - 1] + 0.006f, f));
    return o;
}
static void ZBrand(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.02f;
    switch (id) {
    case 0: {   // Martini stripes
        const NRgb c[5] = {{0.00f, 0.10f, 0.45f}, {0.95f, 0.95f, 0.95f}, {0.20f, 0.60f, 0.95f}, {0.95f, 0.95f, 0.95f}, {0.90f, 0.05f, 0.10f}};
        const float e[5] = {0.34f, 0.40f, 0.66f, 0.72f, 1.0f};
        NRgb o = zBand(u * 0.7f + v * 1.2f - t * 0.25f, c, e, 5);
        float gl = 0.88f + 0.12f * sinf((u - v) * 6.0f - t * 1.5f);
        r = o.r * gl; g = o.g * gl; b = o.b * gl;
        break;
    }
    case 1: {   // Gulf livery
        float f = Fr((u - v * 0.15f) * 2.0f - t * 0.1f), d = fabsf(f - 0.5f);
        float shade = 0.9f + 0.1f * sinf(v * 8.0f + t);
        r = 0.45f * shade; g = 0.72f * shade; b = 0.90f * shade;
        float w = bSm(0.17f, 0.15f, d), o = bSm(0.12f, 0.10f, d);
        r = bMix(r, 0.96f, w); g = bMix(g, 0.96f, w); b = bMix(b, 0.96f, w);
        r = bMix(r, 1.0f, o); g = bMix(g, 0.45f, o); b = bMix(b, 0.02f, o);
        break;
    }
    case 2: {   // Black with gold pinstripes
        float f = Fr(u * 4.0f + v * 0.5f - t * 0.2f);
        float line = nBar(f, 0.46f, 0.54f), thin = nBar(f, 0.20f, 0.23f) * 0.7f;
        float gold = 0.7f + 0.3f * sinf((u + v) * 9.0f - t * 1.5f);
        float k = Cl(line + thin);
        r = 0.03f + 0.97f * gold * k; g = 0.03f + 0.75f * gold * k; b = 0.03f + 0.25f * gold * k;
        break;
    }
    case 3: {   // Fluted green dial with gold ring
        float x = u - 0.5f, y = v - 0.5f, rr = bLen(x, y), ang = atan2f(y, x);
        float fl = 0.5f + 0.5f * cosf(ang * 36.0f);
        float sw = powf(0.5f + 0.5f * cosf(ang * 2.0f - t), 4.0f);
        r = 0.0f + 0.04f * fl + 0.7f * sw * fl; g = 0.20f + 0.20f * fl + 0.5f * sw * fl; b = 0.08f + 0.08f * fl + 0.1f * sw * fl;
        float ring = nBar(Fr(rr * 3.0f), 0.42f, 0.58f);
        bPut(r, g, b, 0.95f, 0.75f, 0.25f, ring * (0.7f + 0.3f * sinf(ang * 6.0f + t)));
        break;
    }
    case 4: {   // Monogram lattice (brown + gold flowers)
        float x = (u + v) * 5.0f, y = (u - v) * 5.0f + t * 0.1f;
        int ix = (int)floorf(x), iy = (int)floorf(y);
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f;
        float par = ((ix + iy) & 1) ? 1.0f : 0.0f;
        r = 0.34f; g = 0.19f; b = 0.09f;
        float dia = fabsf(fx) + fabsf(fy);
        float ang = atan2f(fy, fx), rr = bLen(fx, fy);
        float flower = par > 0.5f ? bSm(0.02f, -0.02f, rr - (0.12f + 0.09f * cosf(4.0f * ang))) : bSm(0.015f, -0.015f, fabsf(dia - 0.28f)) * 0.8f;
        float cdot = bSm(0.05f, 0.03f, rr) * par;
        float lines = bSm(0.015f, 0.0f, fabsf(dia - 0.5f)) * 0.5f;
        float sp = powf(0.5f + 0.5f * sinf((u + v) * 5.0f - t * 1.3f), 10.0f);
        bPut(r, g, b, 0.95f, 0.72f, 0.28f, Cl(flower + cdot * 0.5f + lines) * (0.7f + 0.3f * sp));
        break;
    }
    case 5: {   // Beige tartan
        float a = Fr(u * 3.0f + 0.03f * sinf(t)), c = Fr(v * 3.0f);
        r = 0.80f; g = 0.65f; b = 0.42f;
        for (int k = 0; k < 2; k++) {
            float q = k ? c : a;
            float red = nBar(q, 0.30f, 0.50f), blk = nBar(q, 0.62f, 0.70f), wh = nBar(q, 0.12f, 0.15f);
            bPut(r, g, b, 0.75f, 0.10f, 0.10f, red * 0.55f);
            bPut(r, g, b, 0.05f, 0.05f, 0.05f, blk * 0.75f);
            bPut(r, g, b, 0.95f, 0.93f, 0.85f, wh * 0.7f);
        }
        float tw = 0.94f + 0.06f * sinf((u + v) * 120.0f);
        float sh = 0.95f + 0.05f * sinf((u - v) * 4.0f - t);
        r *= tw * sh; g *= tw * sh; b *= tw * sh;
        break;
    }
    case 6: {   // Blue & silver energy stripes
        const NRgb c[5] = {{0.05f, 0.10f, 0.50f}, {0.80f, 0.82f, 0.88f}, {0.05f, 0.10f, 0.50f}, {1.0f, 0.82f, 0.05f}, {0.05f, 0.10f, 0.50f}};
        const float e[5] = {0.35f, 0.45f, 0.78f, 0.86f, 1.0f};
        NRgb o = zBand((u + v * 0.5f) * 2.5f - t * 0.3f, c, e, 5);
        r = o.r; g = o.g; b = o.b;
        float sp = Hh((int)(u * 40), (int)(v * 40), (int)(t * 6.0f)) > 0.985f ? 1.0f : 0.0f;
        r += sp; g += sp; b += sp;
        break;
    }
    case 7: {   // Pink & orange donut dots
        float x = u * 5.0f, y = v * 5.0f + t * 0.15f; int iy = (int)floorf(y);
        x += (iy & 1) * 0.5f;
        int ix = (int)floorf(x);
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f, d = bLen(fx, fy);
        float R = 0.34f + 0.05f * sinf(t * 2.0f + Hh(ix, iy, 5) * 9.0f);
        r = 1.0f; g = 0.30f; b = 0.60f;
        float ring = bSm(R, R - 0.03f, d) * bSm(R * 0.38f, R * 0.38f + 0.03f, d);
        float hl = 0.85f + 0.15f * Cl(1.0f - bLen(fx + 0.1f, fy + 0.1f) * 3.0f);
        bPut(r, g, b, 1.0f * hl, 0.50f * hl, 0.10f * hl, ring);
        break;
    }
    case 8: {   // Yellow & black hazard stripes
        float f = Fr((u + v) * 6.0f - t * 0.5f);
        float m = bSm(0.48f, 0.52f, f) * bSm(1.0f, 0.96f, f);
        float scuff = bFbm(u * 14.0f, v * 14.0f);
        float sh = 0.9f + 0.1f * sinf((u - v) * 5.0f + t);
        float y = 1.0f - m;
        r = (0.04f + 0.96f * y) * (0.85f + 0.15f * scuff) * sh; g = (0.04f + 0.78f * y) * (0.85f + 0.15f * scuff) * sh; b = (0.04f + 0.02f * y) * sh;
        break;
    }
    case 9: {   // Racing tricolour: light blue / dark blue / red
        const NRgb c[7] = {{0.35f, 0.70f, 1.0f}, {0.95f, 0.95f, 0.95f}, {0.05f, 0.10f, 0.55f}, {0.95f, 0.95f, 0.95f}, {0.85f, 0.05f, 0.10f}, {0.04f, 0.04f, 0.05f}, {0.35f, 0.70f, 1.0f}};
        const float e[7] = {0.22f, 0.26f, 0.48f, 0.52f, 0.74f, 0.80f, 1.0f};
        NRgb o = zBand(u * 1.6f + v * 0.6f - t * 0.2f, c, e, 7);
        float gl = 0.8f + 0.2f * powf(0.5f + 0.5f * sinf((u + v) * 4.0f - t * 1.4f), 3.0f) + 0.1f * (1.0f - v);
        r = o.r * gl; g = o.g * gl; b = o.b * gl;
        break;
    }
    case 10: {  // Silver brushed metal with chevrons
        int row = (int)floorf(v * 140.0f);
        float rn = Hh(row, 0, 3);
        float sweep = powf(0.5f + 0.5f * sinf(u * 3.0f - t * 0.9f + rn * 0.5f), 6.0f);
        float c = 0.55f + 0.2f * rn + 0.35f * sweep;
        float ch = fabsf(Fr(v * 3.0f + fabsf(u - 0.5f) * 1.2f) - 0.5f);
        float line = bSm(0.015f, 0.0f, ch - 0.47f);
        c *= 1.0f - 0.5f * line;
        r = c * 0.88f; g = c * 0.90f; b = c * 0.95f;
        break;
    }
    case 11: {  // Blue / black wavy split
        float s = v + 0.07f * sinf(u * 6.0f + t * 1.3f) + 0.03f * sinf(u * 15.0f - t * 2.0f) - 0.5f;
        float bl = bSm(0.004f, -0.004f, s);
        float gl = 0.75f + 0.25f * powf(0.5f + 0.5f * sinf(u * 4.0f - v * 2.0f - t), 3.0f);
        r = bMix(0.03f, 0.0f, bl); g = bMix(0.03f, 0.25f * gl, bl); b = bMix(0.04f, 0.95f * gl, bl);
        float line = bSm(0.02f, 0.0f, fabsf(s));
        r += 0.4f * line; g += 0.7f * line; b += 1.0f * line * 0.8f;
        break;
    }
    case 12: {  // Papaya orange + speed streaks
        int row = (int)floorf(v * 16.0f); float h = Hh(row, 0, 9), fy = fabsf(Fr(v * 16.0f) - 0.5f);
        float x = Fr(u * 0.5f - t * (0.3f + 0.6f * h) + h), len = 0.08f + 0.3f * Hh(row, 1, 9);
        float st = nBar(x, 0.0f, len) * bSm(0.45f, 0.35f, fy) * (h > 0.35f ? 1.0f : 0.0f);
        float sh = 0.9f + 0.1f * sinf(v * 5.0f + t);
        r = 1.0f * sh; g = 0.50f * sh; b = 0.0f;
        bPut(r, g, b, 0.04f, 0.04f, 0.05f, st);
        break;
    }
    case 13: {  // Red / white / blue swirl
        float x = u - 0.5f, y = v - 0.5f, rr = bLen(x, y), ang = atan2f(y, x);
        const NRgb c[3] = {{0.90f, 0.05f, 0.10f}, {0.97f, 0.97f, 0.97f}, {0.05f, 0.20f, 0.75f}};
        const float e[3] = {0.34f, 0.66f, 1.0f};
        NRgb o = zBand(ang / kTau * 3.0f + rr * 1.5f - t * 0.2f + 0.08f * sinf(rr * 12.0f - t), c, e, 3);
        float sh = 0.85f + 0.15f * cosf(rr * 6.0f - t);
        r = o.r * sh; g = o.g * sh; b = o.b * sh;
        break;
    }
    case 14: {  // Sunset social gradient
        float f = Cl(u * 0.5f + (1.0f - v) * 0.8f + 0.2f * bFbm(u * 3.0f + t * 0.2f, v * 3.0f) + 0.1f * sinf(t * 0.5f) - 0.05f);
        const NRgb s0 = {0.30f, 0.10f, 0.80f}, s1 = {0.85f, 0.15f, 0.55f}, s2 = {1.0f, 0.45f, 0.15f}, s3 = {1.0f, 0.85f, 0.25f};
        NRgb o = nMix(s0, s1, bSm(0.0f, 0.4f, f)); o = nMix(o, s2, bSm(0.4f, 0.75f, f)); o = nMix(o, s3, bSm(0.75f, 1.0f, f));
        float gl = xGl(bLen(u - 0.5f - 0.3f * sinf(t * 0.6f), v - 0.5f), 6.0f) * 0.18f;
        r = o.r + gl; g = o.g + gl; b = o.b + gl;
        break;
    }
    case 15: {  // Toy bricks with studs
        float x = u * 4.0f, y = v * 4.0f; int ix = (int)floorf(x), iy = (int)floorf(y);
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f;
        static const NRgb P[5] = {{0.85f, 0.05f, 0.08f}, {0.05f, 0.30f, 0.85f}, {1.0f, 0.82f, 0.05f}, {0.05f, 0.60f, 0.20f}, {0.95f, 0.95f, 0.95f}};
        int ci = (ix + iy * 3 + (int)floorf(t * 0.5f)) % 5;
        NRgb c = P[ci];
        float gap = bSm(0.46f, 0.5f, bMax(fabsf(fx), fabsf(fy)));
        float d = bLen(fx, fy);
        float stud = bSm(0.30f, 0.28f, d), rim = bSm(0.30f, 0.26f, d) * bSm(0.20f, 0.26f, d);
        float hl = 1.0f + 0.35f * stud * Cl(1.0f - bLen(fx + 0.08f, fy + 0.08f) * 4.0f);
        r = c.r * (0.85f + 0.15f * stud) * hl + 0.12f * rim; g = c.g * (0.85f + 0.15f * stud) * hl + 0.12f * rim; b = c.b * (0.85f + 0.15f * stud) * hl + 0.12f * rim;
        r *= 1.0f - 0.7f * gap; g *= 1.0f - 0.7f * gap; b *= 1.0f - 0.7f * gap;
        float sd = bSm(0.30f, 0.38f, d) * bSm(0.45f, 0.30f, d) * (fx > 0.0f && fy > 0.0f ? 0.3f : 0.0f);
        r *= 1.0f - sd; g *= 1.0f - sd; b *= 1.0f - sd;
        break;
    }
    case 16: {  // Pixel blocks (grass / dirt / stone) scrolling
        const float N = 16.0f;
        float x = u * N + t * 1.5f, y = v * N;
        int ix = (int)floorf(x), iy = (int)floorf(y);
        int ground = 5 + (int)(Hh(ix / 3, 0, 5) * 3.0f);
        float tone = 0.85f + 0.15f * Hh(ix, iy, 3), px = Fr(x), py = Fr(y);
        if (iy < ground) {
            r = 0.45f; g = 0.75f; b = 1.0f;
            float cl = Hh(ix / 4, iy, 8) > 0.82f && iy < 4 ? 1.0f : 0.0f;
            r = bMix(r, 1.0f, cl); g = bMix(g, 1.0f, cl); b = bMix(b, 1.0f, cl);
        } else if (iy == ground) { r = 0.30f * tone; g = 0.70f * tone; b = 0.20f * tone; }
        else if (iy <= ground + 2) { r = 0.50f * tone; g = 0.33f * tone; b = 0.20f * tone; }
        else {
            r = 0.50f * tone; g = 0.50f * tone; b = 0.52f * tone;
            float h = Hh(ix, iy, 9);
            if (h > 0.90f) { r = 0.1f; g = 0.1f; b = 0.1f; }
            else if (h > 0.86f) { r = 0.95f; g = 0.8f; b = 0.2f; }
            else if (h > 0.83f) { r = 0.3f; g = 0.95f; b = 0.95f; }
        }
        float ed = bMin(bMin(px, 1.0f - px), bMin(py, 1.0f - py));
        float k = 0.82f + 0.18f * bSm(0.0f, 0.12f, ed);
        r *= k; g *= k; b *= k;
        break;
    }
    case 17: {  // Orange & black flames
        r = g = b = 0.02f;
        for (int k = 0; k < 3; k++) {
            float s = 0.5f + 0.5f * sinf(u * (9.0f + 3.0f * k) + sinf(u * 4.0f + k + t * 1.7f) * 1.4f - t * (2.5f + k));
            float top = 0.25f + 0.14f * k + 0.35f * (1.0f - s);
            float fill = bSm(top, top + 0.012f, v), line = bSm(0.03f, 0.0f, fabsf(v - top));
            static const float CR[3] = {0.65f, 1.0f, 1.0f}, CG[3] = {0.08f, 0.45f, 0.85f}, CB[3] = {0.02f, 0.02f, 0.10f};
            bPut(r, g, b, 0.02f, 0.02f, 0.02f, line);
            bPut(r, g, b, CR[k], CG[k], CB[k], fill * (1.0f - line));
        }
        break;
    }
    case 18: {  // Red & white slashes
        float x = (u - v) * 3.0f + t * 0.4f; int i = (int)floorf(x);
        float f = Fr(x), w = 0.2f + 0.3f * Hh(i, 0, 5);
        float wm = bSm(0.0f, 0.02f, f) * bSm(w + 0.02f, w, f);
        float sh = 0.9f + 0.1f * sinf((u + v) * 5.0f - t);
        r = bMix(0.85f, 0.98f, wm) * sh; g = bMix(0.05f, 0.98f, wm) * sh; b = bMix(0.08f, 0.98f, wm) * sh;
        float ln = bSm(0.015f, 0.0f, fabsf(f - w - 0.04f)) * 0.8f;
        r = bMix(r, 0.04f, ln); g = bMix(g, 0.04f, ln); b = bMix(b, 0.04f, ln);
        break;
    }
    case 19: {  // Hot pink glitter
        float n = bFbm(u * 3.0f + t * 0.15f, v * 3.0f);
        r = bMix(1.0f, 0.75f, n); g = bMix(0.25f, 0.05f, n); b = bMix(0.65f, 0.50f, n);
        int cx = (int)floorf(u * 40.0f), cy = (int)floorf(v * 40.0f);
        float h = Hh(cx, cy, (int)floorf(t * 3.0f + Hh(cx, cy, 1) * 6.0f));
        float sp = h > 0.9f ? 1.0f : 0.0f, mid = (h > 0.7f && h <= 0.9f) ? 0.25f : 0.0f;
        r += sp + mid * 0.6f; g += sp * 0.9f + mid * 0.3f; b += sp + mid * 0.5f;
        break;
    }
    default: {  // 20 Electric red with charge lines
        float vg = 0.6f + 0.4f * (1.0f - v);
        r = 0.65f * vg; g = 0.02f; b = 0.05f * vg;
        int row = (int)floorf(v * 10.0f); float h = Hh(row, 0, 11);
        float ly = fabsf(Fr(v * 10.0f) - 0.5f);
        float line = bSm(0.07f, 0.0f, ly);
        float pulse = bSm(0.40f, 0.0f, Fr(u - t * (0.3f + 0.4f * h) + h));
        float base = line * 0.25f;
        r += base * 0.5f; g += base * 0.5f; b += base * 0.8f;
        float k = line * pulse;
        r += 0.6f * k; g += 0.9f * k; b += 1.0f * k;
        break;
    }
    }
}

// ---------------------------------------- FOOD & FUN (22 new, ids 362..383) ----------------------------------------
static void ZFun(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.02f;
    switch (id) {
    case 0: {   // Pepperoni pizza
        float n = bFbm(u * 6.0f + t * 0.05f, v * 6.0f), bub = bSm(0.62f, 0.7f, bFbm(u * 14.0f, v * 14.0f - t * 0.3f));
        r = 1.0f * (0.85f + 0.15f * n); g = 0.78f * (0.85f + 0.15f * n); b = 0.30f * (0.8f + 0.2f * n);
        r += 0.08f * bub; g += 0.06f * bub;
        float x = u * 4.0f + t * 0.05f, y = v * 4.0f; int ix = (int)floorf(x), iy = (int)floorf(y);
        float fx = Fr(x) - 0.5f - (Hh(ix, iy, 2) - 0.5f) * 0.3f, fy = Fr(y) - 0.5f - (Hh(ix, iy, 3) - 0.5f) * 0.3f;
        float d = bLen(fx, fy), R = 0.30f + 0.06f * Hh(ix, iy, 4);
        float pep = bSm(R, R - 0.03f, d) * (Hh(ix, iy, 5) > 0.15f ? 1.0f : 0.0f);
        float rim = bSm(R * 0.82f, R * 0.95f, d);
        float gr = 0.5f + 0.5f * sinf(t * 1.5f + Hh(ix, iy, 6) * 9.0f);
        bPut(r, g, b, 0.78f, 0.15f, 0.10f, pep);
        bPut(r, g, b, 0.50f, 0.08f, 0.05f, pep * rim * 0.8f);
        float hl = pep * bSm(0.10f, 0.0f, bLen(fx + 0.08f, fy + 0.08f)) * (0.3f + 0.3f * gr);
        r += hl; g += hl * 0.7f; b += hl * 0.5f;
        float gp = Hh((int)(u * 22), (int)(v * 22), 7) > 0.93f ? 1.0f : 0.0f;
        bPut(r, g, b, 0.15f, 0.55f, 0.15f, gp * (1.0f - pep));
        break;
    }
    case 1: {   // Donut glaze with drips + sprinkles
        float drip = 0.55f + 0.10f * sinf(u * 9.0f + t * 0.8f) + 0.14f * powf(0.5f + 0.5f * sinf(u * 5.0f - t * 0.5f), 4.0f) + 0.10f * powf(0.5f + 0.5f * sinf(u * 13.0f + 2.0f + t * 0.7f), 6.0f);
        float dough = 0.85f + 0.15f * bFbm(u * 10.0f, v * 10.0f);
        r = 0.88f * dough; g = 0.60f * dough; b = 0.30f * dough;
        float gl = bSm(drip + 0.01f, drip - 0.01f, v);
        float sh = 0.9f + 0.1f * sinf(u * 6.0f + v * 4.0f - t);
        NRgb bg = {1.0f * sh, 0.45f * sh, 0.70f * sh};
        float sr, sg, sb; NPieces(u, v, t, 10.0f, 0.15f, 0, bg, sr, sg, sb);
        r = bMix(r, sr, gl); g = bMix(g, sg, gl); b = bMix(b, sb, gl);
        float spec = bSm(0.03f, 0.0f, fabsf(v - drip + 0.04f)) * gl * 0.3f;
        r += spec; g += spec; b += spec;
        break;
    }
    case 2: {   // Ice cream swirl (neapolitan)
        const NRgb c[3] = {{0.35f, 0.17f, 0.08f}, {1.0f, 0.60f, 0.72f}, {1.0f, 0.95f, 0.75f}};
        const float e[3] = {0.33f, 0.66f, 1.0f};
        float f = u * 3.0f + 0.35f * sinf(v * 7.0f + t) + v * 1.2f + t * 0.1f;
        NRgb o = zBand(f, c, e, 3);
        float sh = 0.75f + 0.25f * cosf(Fr(f) * kTau * 3.0f);
        float sp = powf(0.5f + 0.5f * sinf(u * 5.0f - v * 3.0f - t), 8.0f) * 0.25f;
        r = o.r * sh + sp; g = o.g * sh + sp; b = o.b * sh + sp;
        break;
    }
    case 3: {   // Burger layers
        float w = 0.02f * sinf(u * 14.0f + t * 1.2f);
        float y = v + w;
        r = 0.55f; g = 0.35f; b = 0.12f;
        if (y < 0.26f) {          // top bun + sesame
            float k = 0.9f - 0.4f * (0.26f - y) * 3.0f;
            r = 0.92f * k; g = 0.62f * k; b = 0.22f * k;
            float x = u * 9.0f, yy = v * 9.0f; int ix = (int)floorf(x), iy = (int)floorf(yy);
            float fx = Fr(x) - 0.5f - (Hh(ix, iy, 2) - 0.5f) * 0.4f, fy = Fr(yy) - 0.5f - (Hh(ix, iy, 3) - 0.5f) * 0.4f;
            float s = bSm(0.09f, 0.06f, bLen(fx * 1.0f, fy * 2.0f)) * (Hh(ix, iy, 4) > 0.3f ? 1.0f : 0.0f);
            bPut(r, g, b, 0.98f, 0.92f, 0.75f, s);
        } else if (y < 0.34f) {   // lettuce
            float k = 0.7f + 0.3f * sinf(u * 30.0f + t);
            r = 0.30f * k; g = 0.75f * k; b = 0.15f * k;
        } else if (y < 0.42f) { r = 0.88f; g = 0.12f; b = 0.10f; }   // tomato
        else if (y < 0.50f) { r = 1.0f; g = 0.78f; b = 0.10f; }       // cheese
        else if (y < 0.70f) {     // patty
            float n = bFbm(u * 12.0f, v * 12.0f);
            r = 0.30f * (0.7f + 0.5f * n); g = 0.14f * (0.7f + 0.5f * n); b = 0.07f * (0.7f + 0.5f * n);
        } else if (y < 0.76f) { r = 0.35f; g = 0.78f; b = 0.18f; }
        else { r = 0.88f * (1.0f - 0.3f * (y - 0.76f)); g = 0.58f * (1.0f - 0.3f * (y - 0.76f)); b = 0.20f; }
        float sh = 0.92f + 0.08f * sinf(u * 4.0f - t * 1.2f);
        r *= sh; g *= sh; b *= sh;
        break;
    }
    case 4: {   // Sushi rolls on a bamboo mat
        r = 0.72f + 0.1f * sinf(u * 90.0f); g = 0.58f + 0.08f * sinf(u * 90.0f); b = 0.32f;
        float x = u * 3.0f + t * 0.2f, y = v * 3.0f; int ix = (int)floorf(x), iy = (int)floorf(y);
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f, d = bLen(fx, fy);
        float h = Hh(ix, iy, 21);
        bPut(r, g, b, 0.03f, 0.06f, 0.04f, bSm(0.42f, 0.40f, d));
        bPut(r, g, b, 0.97f, 0.97f, 0.93f, bSm(0.36f, 0.34f, d));
        float rs = Hh((int)(u * 150), (int)(v * 150), 3) > 0.8f ? 0.08f : 0.0f;
        r -= rs * bSm(0.36f, 0.34f, d); g -= rs * bSm(0.36f, 0.34f, d);
        float c = bSm(0.17f, 0.15f, d);
        if (h < 0.34f) bPut(r, g, b, 1.0f, 0.45f, 0.30f, c);
        else if (h < 0.67f) bPut(r, g, b, 0.35f, 0.75f, 0.25f, c);
        else bPut(r, g, b, 0.80f, 0.10f, 0.15f, c);
        r += 0.15f * bSm(0.08f, 0.0f, bLen(fx + 0.06f, fy + 0.06f)) * c;
        break;
    }
    case 5: {   // Popcorn popping
        r = 0.90f; g = 0.70f; b = 0.30f;
        float x = u * 4.0f, y = v * 4.0f; int ix = (int)floorf(x), iy = (int)floorf(y);
        for (int j = -1; j <= 1; j++) for (int i = -1; i <= 1; i++) {
            int ci = ix + i, cj = iy + j;
            float h = Hh(ci, cj, 17);
            float s = 0.7f + 0.3f * fabsf(sinf(t * 2.0f + h * 20.0f));
            float cx = i + 0.5f + (h - 0.5f) * 0.4f, cy = j + 0.5f + (Hh(ci, cj, 18) - 0.5f) * 0.4f;
            float px = Fr(x) - cx, py = Fr(y) - cy;
            float d = bMin(bLen(px - 0.12f * s, py) - 0.16f * s, bMin(bLen(px + 0.12f * s, py + 0.04f) - 0.15f * s, bLen(px, py - 0.12f * s) - 0.15f * s));
            float cov = bEdge(d);
            if (cov > 0.01f) {
                float k = Cl(1.0f + d * 3.0f);
                float cr = bMix(1.0f, 0.95f, 1.0f - k), cg = bMix(0.97f, 0.78f, 1.0f - k), cb = bMix(0.85f, 0.35f, 1.0f - k);
                bPut(r, g, b, cr, cg, cb, cov);
                bPut(r, g, b, 0.55f, 0.35f, 0.10f, cov * bSm(0.05f, 0.0f, bLen(px, py + 0.13f)) * 0.8f);
            }
        }
        break;
    }
    case 6: {   // Swiss cheese
        float fill, inner, h; nSpots(u, v, 5.0f, t, 0.12f, 0.2f, 0.18f, 0.34f, fill, inner, h);
        float n = bFbm(u * 7.0f, v * 7.0f);
        r = 1.0f * (0.9f + 0.1f * n); g = 0.82f * (0.9f + 0.1f * n); b = 0.25f * (0.9f + 0.1f * n);
        float ring = Cl(fill - inner);
        bPut(r, g, b, 0.90f, 0.65f, 0.15f, ring);
        bPut(r, g, b, 0.55f, 0.35f, 0.05f, inner);
        break;
    }
    case 7: {   // Strawberry skin with seeds
        float y = v * 11.0f; int iy = (int)floorf(y);
        float x = u * 11.0f + (iy & 1) * 0.5f + 0.2f * sinf(t * 0.6f); int ix = (int)floorf(x);
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f;
        float d = bLen(fx, fy * 0.8f);
        float sh = 0.8f + 0.2f * (1.0f - v);
        r = 0.90f * sh; g = 0.05f * sh; b = 0.12f * sh;
        float dim = bSm(0.40f, 0.10f, d) * 0.35f;
        r *= 1.0f - dim; g *= 1.0f - dim; b *= 1.0f - dim;
        float seed = bEdge(bLen(fx, (fy - 0.02f) * 0.7f) - 0.12f);
        bPut(r, g, b, 1.0f, 0.85f, 0.3f, seed);
        float gl = powf(0.5f + 0.5f * sinf(u * 4.0f - v * 3.0f - t * 1.2f), 10.0f) * 0.35f;
        r += gl; g += gl; b += gl;
        (void)ix;
        break;
    }
    case 8: {   // Orange slice
        float x = u - 0.5f, y = v - 0.5f, rr = bLen(x, y), ang = atan2f(y, x) + t * 0.05f;
        float seg = Fr(ang / kTau * 10.0f);
        float wall = bSm(0.04f, 0.0f, xEdge(seg) * 1.0f) * bSm(0.05f, 0.1f, rr);
        float vs = bFbm(u * 40.0f, v * 40.0f + t * 0.2f);
        r = 1.0f; g = 0.55f + 0.2f * vs; b = 0.05f + 0.08f * vs;
        float gl = 0.8f + 0.2f * sinf(ang * 5.0f + rr * 20.0f - t * 2.0f);
        r *= gl; g *= gl;
        bPut(r, g, b, 1.0f, 0.95f, 0.8f, wall);
        bPut(r, g, b, 1.0f, 0.95f, 0.8f, bSm(0.07f, 0.04f, rr));
        float rind = bSm(0.43f, 0.47f, rr);
        bPut(r, g, b, 1.0f, 0.96f, 0.82f, rind * bSm(0.5f, 0.47f, rr));
        bPut(r, g, b, 0.95f, 0.50f, 0.02f, bSm(0.47f, 0.50f, rr));
        break;
    }
    case 9: {   // Kiwi slice
        float x = u - 0.5f, y = v - 0.5f, rr = bLen(x, y), ang = atan2f(y, x) + t * 0.04f;
        float st = 0.5f + 0.5f * sinf(ang * 60.0f);
        float k = bSm(0.0f, 0.4f, rr);
        r = bMix(0.55f, 0.35f, k) + 0.08f * st; g = bMix(0.85f, 0.75f, k) + 0.05f * st; b = bMix(0.35f, 0.12f, k);
        bPut(r, g, b, 0.95f, 0.97f, 0.80f, bSm(0.12f, 0.06f, rr));
        float lane = Fr(ang / kTau * 28.0f) - 0.5f;
        float tang = lane * rr * kTau / 28.0f, rad = rr - 0.2f;
        float seed = bSm(0.016f, 0.008f, bLen(tang * 1.2f, rad * 0.8f));
        bPut(r, g, b, 0.04f, 0.03f, 0.02f, seed);
        bPut(r, g, b, 0.45f, 0.30f, 0.15f, bSm(0.46f, 0.50f, rr));
        break;
    }
    case 10: {  // Chomper dots
        r = 0.0f; g = 0.0f; b = 0.12f;
        float y = v * 3.0f; int row = (int)floorf(y); float fy = Fr(y) - 0.5f;
        float h = Hh(row, 0, 3);
        float px = Fr(t * (0.12f + 0.1f * h) + h) * 1.5f - 0.25f;
        float dx = u - px, dy = fy / 3.0f;
        bPut(r, g, b, 0.15f, 0.15f, 0.55f, bSm(0.012f, 0.0f, fabsf(fy) - 0.46f));
        float dd = bLen((Fr(u * 12.0f) - 0.5f) / 12.0f, dy);
        bPut(r, g, b, 1.0f, 0.85f, 0.7f, bSm(0.012f, 0.008f, dd) * (u > px + 0.06f ? 1.0f : 0.0f));
        float mo = 0.15f + 0.55f * fabsf(sinf(t * 10.0f));
        float a = atan2f(dy, dx);
        float pac = bSm(0.106f, 0.1f, bLen(dx, dy)) * ((fabsf(a) > mo) ? 1.0f : 0.0f);
        bPut(r, g, b, 1.0f, 0.9f, 0.05f, pac);
        float gx = u - (px + 0.3f), gy = dy;
        float body = gy < 0.0f ? bLen(gx, gy) - 0.09f : bMax(fabsf(gx) - 0.09f, gy - 0.08f - 0.015f * sinf(gx * 90.0f + t * 12.0f));
        bPut(r, g, b, 0.2f, 0.3f, 1.0f, bEdge(body));
        float eyes = bMin(bLen(gx - 0.03f, gy + 0.01f), bLen(gx + 0.03f, gy + 0.01f));
        bPut(r, g, b, 1.0f, 1.0f, 1.0f, bSm(0.02f, 0.012f, eyes) * bEdge(body));
        break;
    }
    case 11: {  // Falling blocks
        r = g = b = 0.03f;
        float x = u * 10.0f; int cx = (int)floorf(x);
        float sp = 0.4f + 0.8f * Hh(cx, 0, 3);
        float yy = v * 10.0f + t * sp; int cy = (int)floorf(yy);
        float fx = Fr(x), fy = Fr(yy);
        float h = Hh(cx, cy, 4);
        bPut(r, g, b, 0.10f, 0.10f, 0.16f, bSm(0.04f, 0.0f, bMin(bMin(fx, 1.0f - fx), bMin(fy, 1.0f - fy))));
        if (h > 0.45f) {
            static const NRgb P[7] = {{0.0f, 0.9f, 0.95f}, {0.95f, 0.9f, 0.1f}, {0.7f, 0.2f, 0.9f}, {0.2f, 0.85f, 0.25f}, {0.95f, 0.15f, 0.15f}, {0.15f, 0.25f, 0.95f}, {1.0f, 0.55f, 0.05f}};
            NRgb c = P[(int)(Hh(cx, cy, 5) * 7.0f) % 7];
            float bev = fx < 0.12f || fy < 0.12f ? 1.3f : ((fx > 0.88f || fy > 0.88f) ? 0.6f : 1.0f);
            float e = bMax(fabsf(fx - 0.5f), fabsf(fy - 0.5f));
            float cov = bSm(0.5f, 0.46f, e);
            bPut(r, g, b, c.r * bev, c.g * bev, c.b * bev, cov);
        }
        break;
    }
    case 12: {  // Cube stickers sliding
        float y = v * 6.0f; int iy = (int)floorf(y);
        float ph = t * 0.5f + iy * 0.37f, k = floorf(ph), f = Fr(ph), e = f * f * (3.0f - 2.0f * f);
        float dir = (iy & 1) ? 1.0f : -1.0f;
        float x = u * 6.0f + (k + e) * dir;
        int ix = (int)floorf(x);
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f;
        static const NRgb P[6] = {{0.9f, 0.1f, 0.1f}, {1.0f, 0.5f, 0.05f}, {1.0f, 0.9f, 0.1f}, {0.1f, 0.7f, 0.2f}, {0.1f, 0.3f, 0.9f}, {0.95f, 0.95f, 0.95f}};
        NRgb c = P[(((ix + iy) % 6) + 6) % 6];
        float ed = bMax(fabsf(fx), fabsf(fy));
        float cov = bSm(0.46f, 0.42f, ed);
        float gl = 0.85f + 0.15f * Cl(1.0f - bLen(fx + 0.15f, fy + 0.15f) * 2.0f);
        r = 0.02f + c.r * gl * cov; g = 0.02f + c.g * gl * cov; b = 0.02f + c.b * gl * cov;
        break;
    }
    case 13: {  // Tumbling dice
        r = 0.05f; g = 0.30f + 0.05f * bFbm(u * 10.0f, v * 10.0f); b = 0.12f;
        float x = u * 3.0f, y = v * 3.0f; int ix = (int)floorf(x), iy = (int)floorf(y);
        float px = Fr(x) - 0.5f, py = Fr(y) - 0.5f;
        float h = Hh(ix, iy, 31);
        float a = 0.35f * sinf(t * 1.1f + h * 20.0f);
        float c = cosf(a), s = sinf(a), qx = px * c + py * s, qy = -px * s + py * c;
        float d = xBox(qx, qy, 0.32f, 0.32f) - 0.07f;
        int val = 1 + (int)(Hh(ix, iy, (int)floorf(t * 0.8f + h * 5.0f)) * 5.99f);
        static const int MASK[7] = {0, 16, 257, 273, 325, 341, 365};
        int m = MASK[val];
        bPut(r, g, b, 0.0f, 0.0f, 0.0f, bEdge(d - 0.015f) * 0.5f);
        float die = bEdge(d);
        float sh = 0.9f + 0.1f * (qx + qy);
        bPut(r, g, b, 0.96f * sh, 0.94f * sh, 0.88f * sh, die);
        float pip = 0.0f;
        for (int k = 0; k < 9; k++) if (m & (1 << k)) pip = bMax(pip, bEdge(bLen(qx - ((k % 3) - 1) * 0.2f, qy - ((k / 3) - 1) * 0.2f) - 0.055f));
        bPut(r, g, b, 0.04f, 0.04f, 0.05f, pip * die);
        break;
    }
    case 14: {  // Poker chips
        r = 0.02f; g = 0.30f; b = 0.12f;
        r += 0.02f * bFbm(u * 20.0f, v * 20.0f);
        float x = u * 3.0f, y = v * 3.0f + (floorf(u * 3.0f) > 0.5f ? 0.0f : 0.0f); int ix = (int)floorf(x), iy = (int)floorf(y);
        float px = Fr(x) - 0.5f, py = Fr(y) - 0.5f + 0.02f * sinf(t * 1.5f + ix * 2.0f + iy);
        float d = bLen(px, py), ang = atan2f(py, px) + t * 0.3f * (((ix + iy) & 1) ? 1.0f : -1.0f);
        static const NRgb P[5] = {{0.85f, 0.08f, 0.10f}, {0.10f, 0.25f, 0.85f}, {0.08f, 0.08f, 0.10f}, {0.10f, 0.65f, 0.25f}, {0.60f, 0.15f, 0.70f}};
        NRgb c = P[(ix + iy * 2) % 5];
        float R = 0.40f;
        float chip = bSm(R, R - 0.02f, d);
        float notch = Fr(ang / kTau * 8.0f);
        float edge = bSm(R * 0.80f, R * 0.82f, d);
        float wn = nBar(notch, 0.0f, 0.5f);
        bPut(r, g, b, 0.0f, 0.0f, 0.0f, bSm(R + 0.03f, R, d) * 0.4f);
        bPut(r, g, b, c.r, c.g, c.b, chip);
        bPut(r, g, b, 0.95f, 0.95f, 0.95f, chip * edge * wn);
        bPut(r, g, b, 0.95f, 0.95f, 0.95f, bSm(0.012f, 0.0f, fabsf(d - R * 0.62f)));
        bPut(r, g, b, c.r * 0.6f, c.g * 0.6f, c.b * 0.6f, bSm(R * 0.50f, R * 0.46f, d));
        break;
    }
    case 15: {  // Bubble tea with tapioca pearls
        float sw = bFbm(u * 4.0f + t * 0.1f, v * 4.0f - t * 0.05f);
        float k = Cl(v * 1.1f + 0.2f * sw);
        r = bMix(0.88f, 0.52f, k); g = bMix(0.68f, 0.32f, k); b = bMix(0.48f, 0.18f, k);
        const float COLS = 7.0f;
        int cx = (int)floorf(u * COLS);
        for (int dx = -1; dx <= 1; dx++) for (int j = 0; j < 3; j++) {
            int ci = cx + dx;
            float h = Hh(ci, j, 13);
            float by = 1.1f - Fr(t * (0.03f + 0.04f * Hh(ci, j, 15)) + h) * 1.25f;
            float bx = (ci + 0.2f + 0.6f * Hh(ci, j, 17) + 0.12f * sinf(t * 1.1f + h * 20.0f)) / COLS;
            float rad = 0.05f + 0.015f * Hh(ci, j, 19);
            float dxp = u - bx, dyp = v - by, d = bLen(dxp, dyp);
            float cov = bSm(rad, rad - 0.01f, d);
            if (cov > 0.0f) {
                bPut(r, g, b, 0.14f, 0.07f, 0.04f, cov);
                float hl = bSm(rad * 0.35f, 0.0f, bLen(dxp + rad * 0.35f, dyp + rad * 0.35f)) * cov;
                r += hl * 0.7f; g += hl * 0.65f; b += hl * 0.6f;
            }
        }
        break;
    }
    case 16: {  // Smiley faces
        float x = u * 3.0f, y = v * 3.0f; int ix = (int)floorf(x), iy = (int)floorf(y);
        float h = Hh(ix, iy, 7);
        float px = Fr(x) - 0.5f, py = Fr(y) - 0.5f + 0.03f * sinf(t * 2.0f + h * 20.0f);
        r = 1.0f; g = 0.55f + 0.2f * v; b = 0.15f;
        float d = bLen(px, py) - 0.38f;
        float lit = 0.85f + 0.15f * Cl(1.0f - bLen(px + 0.12f, py + 0.12f) * 2.0f);
        bPut(r, g, b, 0.15f, 0.08f, 0.02f, bEdge(d - 0.02f));
        bPut(r, g, b, 1.0f * lit, 0.85f * lit, 0.10f * lit, bEdge(d));
        float bl = 1.0f - bSm(0.94f, 0.99f, sinf(t * 1.3f + h * 9.0f));
        float eyes = bMin(bEll(px, py, -0.13f, -0.10f, 0.045f, 0.07f * bl + 0.006f), bEll(px, py, 0.13f, -0.10f, 0.045f, 0.07f * bl + 0.006f));
        bPut(r, g, b, 0.10f, 0.06f, 0.02f, bEdge(eyes));
        float c = sinf(t * 1.2f + h * 12.0f);
        float ym = 0.10f + c * (0.12f - px * px * 3.0f);
        float mouth = bSm(0.022f, 0.012f, fabsf(py - ym)) * bSm(0.21f, 0.19f, fabsf(px));
        bPut(r, g, b, 0.10f, 0.06f, 0.02f, mouth);
        break;
    }
    case 17: {  // Floating music notes
        r = 0.10f + 0.05f * v; g = 0.04f; b = 0.20f + 0.1f * v;
        for (int i = 0; i < 5; i++) {
            float ly = 0.35f + i * 0.06f;
            float ln = bSm(0.004f, 0.0f, fabsf(v - ly - 0.01f * sinf(u * 6.0f + t)));
            r += 0.12f * ln; g += 0.10f * ln; b += 0.2f * ln;
        }
        for (int i = 0; i < 10; i++) {
            float h = Hh(i, 1, 17), s = 0.8f + 0.6f * Hh(i, 2, 17);
            float nx = (i + 0.5f) / 10.0f + 0.03f * sinf(t * 1.3f + i * 2.0f);
            float ny = 1.2f - Fr(t * (0.05f + 0.06f * h) + h * 3.0f) * 1.5f;
            float hd = bEll(u, v, nx, ny, 0.035f * s, 0.026f * s);
            float st = bCap(u, v, nx + 0.033f * s, ny, nx + 0.033f * s, ny - 0.14f * s, 0.006f * s);
            float fl = bCap(u, v, nx + 0.033f * s, ny - 0.14f * s, nx + 0.07f * s, ny - 0.09f * s, 0.005f * s);
            float d = bMin(hd, bMin(st, fl));
            float hr, hg, hb; Hsv(h * 1.7f + t * 0.05f, 0.75f, 1.0f, hr, hg, hb);
            r += hr * xGl(d, 700.0f) * 0.5f; g += hg * xGl(d, 700.0f) * 0.5f; b += hb * xGl(d, 700.0f) * 0.5f;
            bPut(r, g, b, hr, hg, hb, bEdge(d));
        }
        break;
    }
    case 18: {  // Pop-art halftone dots
        float x = (u + v) * 0.7071f * 14.0f, y = (u - v) * 0.7071f * 14.0f;
        float fx = Fr(x) - 0.5f, fy = Fr(y) - 0.5f, d = bLen(fx, fy);
        float sz = 0.5f * (0.5f + 0.5f * sinf(u * 3.0f + v * 2.0f - t));
        r = 1.0f; g = 0.90f; b = 0.20f;
        bPut(r, g, b, 0.90f, 0.10f, 0.15f, bSm(sz * 0.7f, sz * 0.7f - 0.05f, d));
        float x2 = (u + v) * 0.7071f * 14.0f + 0.5f, y2 = (u - v) * 0.7071f * 14.0f + 0.5f;
        float d2 = bLen(Fr(x2) - 0.5f, Fr(y2) - 0.5f);
        float sz2 = 0.5f * (0.5f + 0.5f * cosf(u * 2.0f - v * 3.0f + t * 0.8f));
        bPut(r, g, b, 0.10f, 0.55f, 0.95f, bSm(sz2 * 0.35f, sz2 * 0.35f - 0.04f, d2) * 0.9f);
        break;
    }
    case 19: {  // Rainbow flag wave
        float w = 0.05f * sinf(u * 6.0f - t * 3.0f) + 0.02f * sinf(u * 13.0f - t * 4.0f);
        float f = Cl(v + w) * 6.0f; int band = (int)floorf(f); if (band > 5) band = 5;
        static const NRgb P[6] = {{0.90f, 0.10f, 0.12f}, {1.0f, 0.55f, 0.05f}, {1.0f, 0.90f, 0.10f}, {0.10f, 0.70f, 0.25f}, {0.10f, 0.35f, 0.95f}, {0.55f, 0.15f, 0.75f}};
        float sh = 0.8f + 0.2f * cosf(u * 6.0f - t * 3.0f);
        r = P[band].r * sh; g = P[band].g * sh; b = P[band].b * sh;
        break;
    }
    case 20: {  // Jelly beans
        r = 0.97f; g = 0.93f; b = 0.85f;
        float x = u * 5.0f, y = v * 5.0f + t * 0.2f; int ix = (int)floorf(x), iy = (int)floorf(y);
        float fx = Fr(x), fy = Fr(y);
        for (int j = -1; j <= 1; j++) for (int i = -1; i <= 1; i++) {
            int ci = ix + i, cj = iy + j;
            float h1 = Hh(ci, cj, 71), h2 = Hh(ci, cj, 72), h3 = Hh(ci, cj, 73);
            float px = fx - (i + 0.5f + (h1 - 0.5f) * 0.4f), py = fy - (j + 0.5f + (h2 - 0.5f) * 0.4f);
            float ang = h3 * kTau + t * (h1 - 0.5f) * 0.8f, ca = cosf(ang), sa = sinf(ang);
            float qx = px * ca + py * sa, qy = -px * sa + py * ca;
            float d = bCap(qx, qy, -0.14f, 0.0f, 0.14f, 0.0f, 0.15f);
            float cov = bEdge(d);
            if (cov > 0.01f) {
                float hr, hg, hb; Hsv(Hh(ci, cj, 75), 0.85f, 0.95f, hr, hg, hb);
                float shd = 0.75f + 0.25f * Cl(1.0f - (qy + 0.15f) * 3.0f);
                bPut(r, g, b, 0.0f, 0.0f, 0.0f, bEdge(d - 0.02f) * 0.15f);
                bPut(r, g, b, hr * shd, hg * shd, hb * shd, cov);
                float hl = bSm(0.07f, 0.0f, bLen((qx + 0.06f) * 0.6f, qy + 0.08f)) * cov;
                r += hl * 0.8f; g += hl * 0.8f; b += hl * 0.8f;
            }
        }
        break;
    }
    default: {  // 21 Cotton candy
        float wx = bFbm(u * 3.0f + t * 0.1f, v * 3.0f) * 2.0f, wy = bFbm(u * 3.0f + 4.0f, v * 3.0f - t * 0.12f) * 2.0f;
        float m = bFbm(u * 2.5f + wx, v * 2.5f + wy);
        float fib = bVn(u * 60.0f + wx * 10.0f, v * 8.0f + wy * 3.0f);
        float k = Cl(m * 2.0f - 0.25f);
        NRgb a = nMix(NRgb{1.0f, 0.55f, 0.80f}, NRgb{0.62f, 0.82f, 1.0f}, Cl(0.5f + 0.9f * (m - 0.5f) + 0.2f * sinf(u * 3.0f + t * 0.4f)));
        float lum = 0.75f + 0.35f * fib;
        r = bMix(1.0f, a.r * lum, k); g = bMix(0.96f, a.g * lum, k); b = bMix(1.0f, a.b * lum, k);
        r = Cl(r + 0.1f * fib); g = Cl(g + 0.1f * fib); b = Cl(b + 0.1f * fib);
        break;
    }
    }
}

// ids 322..383
static void XV12(int id, float u, float v, float t, float& r, float& g, float& b) {
    r = g = b = 0.0f;
    if (id < X_BRAND12) ZAnimal(id - X_ANIMAL12, u, v, t, r, g, b);
    else if (id < X_FUN12) ZBrand(id - X_BRAND12, u, v, t, r, g, b);
    else ZFun(id - X_FUN12, u, v, t, r, g, b);
}

// ids 175..383
static void XExtra(int id, float u, float v, float t, float& r, float& g, float& b) {
    if (id < X_WATER0) XSpace(id - X_SPACE0, u, v, t, r, g, b);
    else if (id < X_GOLD0) XWater(id - X_WATER0, u, v, t, r, g, b);
    else if (id < X_GOLD_END) XGold(id - X_GOLD0, u, v, t, r, g, b);
    else if (id < X_V11_END) XV11(id, u, v, t, r, g, b);
    else XV12(id, u, v, t, r, g, b);
}

// ids 104..383
static void XPixel(int id, float u, float v, float t, float& r, float& g, float& b) {
    if (id < X_NEON0) MatrixPixelX(id - X_MATRIX0, u, v, t, r, g, b);
    else if (id < X_FIRE0) XNeon(id - X_NEON0, u, v, t, r, g, b);
    else if (id < X_END) XFireIce(id - X_FIRE0, u, v, t, r, g, b);
    else XExtra(id, u, v, t, r, g, b);
}

static uint32_t Pixel(int design, float u, float v, float t) {
    float r = 0, g = 0, b = 0;
    const float kPi = 3.14159265f;
    int mv = MatVariant(design);
    if (mv >= 0) { MatrixPixel(mv, u, v, t, r, g, b); return Pack(r, g, b); }
    if (design >= X_MATRIX0) { XPixel(design, u, v, t, r, g, b); return Pack(r, g, b); }   // v0.9 + v1.0 + v1.1 + v1.2 designs 104..383
    if (design >= 59) { NewPixel(design, u, v, t, r, g, b); return Pack(r, g, b); }
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
    int st = (DesignIsScene(d.design) || XIsFireIce(d.design) || XIsExtra(d.design)) ? 2 : 1;      // the big scenes are drawn at 128x128 and doubled (much cheaper)
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
        { int catRows = (N_DC + 3) / 4; y += catRows * cbh + (catRows - 1) * gap * 0.6f + gap; }
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
        int ns = (MatVariant(d.design) >= 0 || XIsMatrix(d.design)) ? 8 : 4;      // matrix text is sparse: sample more points
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
        Log("---- BodyTex v1.0 loaded ----");
        LogGameVer();
        Events::gameProcessEvent += Process;
        Events::drawHudEvent += DrawHud;
        Events::shutdownRwEvent += Shutdown;
    }
} bodyTexPlugin;

