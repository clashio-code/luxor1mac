/*
 * luxor_mac_loader  --  Milestone 1 (probe)
 *
 * Memuat Luxor.app (Mach-O PowerPC 32-bit big-endian, macOS 10.4) di Linux ARM64
 * dengan emulator CPU Unicorn (PPC32).  Fungsi sistem macOS ditiru (HLE) lewat
 * "trap slot": setiap simbol impor dipetakan ke alamat palsu, dan saat game
 * memanggilnya, loader mencatat nama + argumen lalu mengembalikan nilai.
 *
 * Tujuan M1: sampai ke NSApplicationMain() dengan semua framework termuat,
 * ter-rebase, ter-bind, dan semua static initializer jalan.  Log lengkap ada di
 * loader_log.txt.
 *
 * Build normal : gcc -O2 loader.c -lunicorn ...        (lihat workflow yml)
 * Build dry-run: gcc -O2 -DDRYRUN loader.c             (tanpa emulator, hanya
 *                                                       cek parsing/rebase/bind)
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <time.h>
#include <errno.h>
#include <unistd.h>
#include <ctype.h>
#include <math.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/stat.h>

#ifndef DRYRUN
#include <unicorn/unicorn.h>
static uc_engine *g_uc;
#endif

/* ------------------------------------------------------------------ log */
static FILE *g_logf;
static size_t g_logbytes;
static int g_logcut;
#define LOG_MAX_BYTES 3000000u      /* log dipotong setelah ~3 MB supaya tidak membengkak */
static void LOG(const char *fmt, ...)
{
    if (g_logcut) return;
    va_list ap;
    va_start(ap, fmt);
    int n = vprintf(fmt, ap);
    va_end(ap);
    if (g_logf) {
        va_start(ap, fmt);
        vfprintf(g_logf, fmt, ap);
        va_end(ap);
        fflush(g_logf);
    }
    if (n > 0) g_logbytes += (size_t)n;
    if (g_logbytes > LOG_MAX_BYTES) {
        g_logcut = 1;
        const char *m = "\n[LOG DIPOTONG: melebihi 3 MB, kemungkinan ada pengulangan]\n";
        fputs(m, stdout);
        if (g_logf) { fputs(m, g_logf); fflush(g_logf); }
    }
    fflush(stdout);
}

/* -------------------------------------------------------- big endian io */
static inline uint32_t be32(const uint8_t *p)
{
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | p[3];
}
static inline uint16_t be16(const uint8_t *p) { return (uint16_t)((p[0] << 8) | p[1]); }
static inline void wbe32(uint8_t *p, uint32_t v)
{
    p[0] = v >> 24; p[1] = v >> 16; p[2] = v >> 8; p[3] = (uint8_t)v;
}

/* ------------------------------------------------------ layout memori guest */
#define PAGE_SZ      0x1000u
#define FW_BASE      0x10000000u   /* framework pertama */
#define FW_STRIDE    0x00800000u
#define HEAP_BASE    0x20000000u
#define HEAP_SIZE    0x08000000u   /* 128 MB */
#define DATA_BASE    0x6e000000u   /* blob data simbol HLE */
#define DATA_SIZE    0x00200000u
#define TRAP_BASE    0x6f000000u   /* slot fungsi HLE, 16 byte per slot */
#define TRAP_SIZE    0x00100000u
#define RET_SENTINEL TRAP_BASE     /* slot 0 = penanda "kembali ke loader" */
#define STACK_TOP    0x7ff00000u
#define STACK_SIZE   0x00800000u
#define INIT_SP      0x7f900000u   /* stack untuk memanggil initializer */

typedef struct { uint32_t base, size; uint8_t *host; const char *name; } Region;
static Region g_reg[64];
static int g_nreg;

static uint8_t *map_region(const char *name, uint32_t base, uint32_t size)
{
    void *p = mmap(NULL, size, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (p == MAP_FAILED) { LOG("FATAL: mmap gagal untuk %s (%u bytes)\n", name, size); exit(2); }
#ifndef DRYRUN
    uc_err e = uc_mem_map_ptr(g_uc, base, size, UC_PROT_ALL, p);
    if (e != UC_ERR_OK) { LOG("FATAL: uc_mem_map_ptr %s: %s\n", name, uc_strerror(e)); exit(2); }
#endif
    g_reg[g_nreg++] = (Region){ base, size, (uint8_t *)p, name };
    return (uint8_t *)p;
}

static uint8_t *g2h(uint32_t a, uint32_t len)
{
    for (int i = 0; i < g_nreg; i++) {
        Region *r = &g_reg[i];
        if (a >= r->base && (uint64_t)a + len <= (uint64_t)r->base + r->size)
            return r->host + (a - r->base);
    }
    return NULL;
}

static const char *gstr(uint32_t a)
{
    static char buf[4][160];
    static int n;
    char *o = buf[n++ & 3];
    for (int i = 0; i < g_nreg; i++) {
        Region *r = &g_reg[i];
        if (a >= r->base && a < r->base + r->size) {
            uint32_t room = r->base + r->size - a;
            if (room > 150) room = 150;
            const uint8_t *s = r->host + (a - r->base);
            uint32_t k = 0;
            while (k < room && s[k]) { o[k] = (s[k] >= 32 && s[k] < 127) ? s[k] : '.'; k++; }
            o[k] = 0;
            return o;
        }
    }
    snprintf(o, 160, "<unmapped %08x>", a);
    return o;
}

/* ------------------------------------------------------------- image macho */
typedef struct { char seg[17], name[17]; uint32_t addr, size, off, flags, res1, res2; } Sect;
typedef struct { char name[17]; uint32_t vmaddr, vmsize, fileoff, filesize, prot; } Seg;
typedef struct { uint32_t addr; const char *name; } SymRec;

typedef struct Image {
    char path[600], install[300], short_name[64];
    int is_exe, idx;
    uint32_t slide, lo, hi;
    uint8_t *host;
    uint8_t *file; size_t filesz; const uint8_t *mh;
    uint8_t *rebased;                 /* 1 byte per 4-byte word di [lo,hi) */
    uint32_t symoff, nsyms, stroff, strsize;
    uint32_t ilocal, nlocal, iext, next, iundef, nundef;
    uint32_t indoff, nind, extreloff, nextrel, locreloff, nlocrel;
    Sect sects[80]; int nsects;
    Seg segs[10]; int nsegs;
    char deps[24][600]; int ndeps;
    uint32_t entry; int has_entry;
    SymRec *syms; int nsymrec;
    /* statistik */
    int n_rebase, n_extrel, n_lazy, n_nonlazy, n_nl_local, n_odd_reloc, n_extrel_addend;
} Image;

static Image *g_img[32];
static int g_nimg;
static Image *g_order[32];      /* urutan inisialisasi: dependensi dulu */
static int g_norder;
static char g_exe_dir[600];

/* tabel export global (flat namespace) */
typedef struct { const char *name; uint32_t addr; } Exp;
#define EXP_BITS 17
static Exp g_exp[1 << EXP_BITS];
static size_t g_nexp;

static uint32_t hash_str(const char *s)
{
    uint32_t h = 5381;
    while (*s) h = h * 33 + (uint8_t)*s++;
    return h;
}
static void exp_add(const char *name, uint32_t addr)
{
    uint32_t h = hash_str(name) & ((1 << EXP_BITS) - 1);
    while (g_exp[h].name) {
        if (!strcmp(g_exp[h].name, name)) return;     /* definisi pertama menang */
        h = (h + 1) & ((1 << EXP_BITS) - 1);
    }
    g_exp[h].name = name; g_exp[h].addr = addr; g_nexp++;
}
static int exp_find(const char *name, uint32_t *addr)
{
    uint32_t h = hash_str(name) & ((1 << EXP_BITS) - 1);
    while (g_exp[h].name) {
        if (!strcmp(g_exp[h].name, name)) { *addr = g_exp[h].addr; return 1; }
        h = (h + 1) & ((1 << EXP_BITS) - 1);
    }
    return 0;
}

static const char *sym_name(Image *im, uint32_t idx, uint8_t *type, uint16_t *desc, uint32_t *value)
{
    const uint8_t *e = im->mh + im->symoff + (size_t)idx * 12;
    uint32_t strx = be32(e);
    if (type) *type = e[4];
    if (desc) *desc = be16(e + 6);
    if (value) *value = be32(e + 8);
    return (const char *)(im->mh + im->stroff + strx);
}

static int cmp_symrec(const void *a, const void *b)
{
    uint32_t x = ((const SymRec *)a)->addr, y = ((const SymRec *)b)->addr;
    return x < y ? -1 : x > y;
}

static const char *describe(uint32_t a)
{
    static char buf[4][200];
    static int n;
    char *o = buf[n++ & 3];
    for (int i = 0; i < g_nimg; i++) {
        Image *im = g_img[i];
        if (a >= im->lo && a < im->hi) {
            const char *best = NULL; uint32_t baddr = 0;
            int lo = 0, hi = im->nsymrec - 1;
            while (lo <= hi) {
                int mid = (lo + hi) / 2;
                if (im->syms[mid].addr <= a) { best = im->syms[mid].name; baddr = im->syms[mid].addr; lo = mid + 1; }
                else hi = mid - 1;
            }
            if (best) snprintf(o, 200, "%s+0x%x (%s+0x%x)", im->short_name, a - im->lo, best, a - baddr);
            else snprintf(o, 200, "%s+0x%x", im->short_name, a - im->lo);
            return o;
        }
    }
    if (a >= TRAP_BASE && a < TRAP_BASE + TRAP_SIZE) snprintf(o, 200, "<trap %08x>", a);
    else snprintf(o, 200, "%08x", a);
    return o;
}

static Image *find_loaded(const char *install)
{
    for (int i = 0; i < g_nimg; i++)
        if (!strcmp(g_img[i]->install, install)) return g_img[i];
    return NULL;
}

static void resolve_path(const char *install, char *out, size_t n)
{
    if (!strncmp(install, "@executable_path", 16))
        snprintf(out, n, "%s%s", g_exe_dir, install + 16);
    else
        snprintf(out, n, "%s", install);
}

static Image *load_image(const char *install, int is_exe)
{
    Image *im = calloc(1, sizeof(Image));
    snprintf(im->install, sizeof im->install, "%s", install);
    resolve_path(install, im->path, sizeof im->path);
    im->is_exe = is_exe;

    FILE *f = fopen(im->path, "rb");
    if (!f) { LOG("FATAL: tidak bisa membuka %s\n", im->path); exit(2); }
    fseek(f, 0, SEEK_END); im->filesz = ftell(f); fseek(f, 0, SEEK_SET);
    im->file = malloc(im->filesz);
    if (fread(im->file, 1, im->filesz, f) != im->filesz) { LOG("FATAL: baca %s gagal\n", im->path); exit(2); }
    fclose(f);

    const uint8_t *mh = im->file;
    if (be32(mh) == 0xcafebabe) {                       /* fat */
        uint32_t n = be32(mh + 4), off = 0;
        for (uint32_t i = 0; i < n; i++) {
            const uint8_t *fa = mh + 8 + i * 20;
            if (be32(fa) == 18) { off = be32(fa + 8); break; }   /* CPU_TYPE_POWERPC */
        }
        if (!off) { LOG("FATAL: %s tidak punya slice PPC\n", im->path); exit(2); }
        mh += off;
    }
    if (be32(mh) != 0xfeedface) { LOG("FATAL: %s bukan Mach-O PPC32 (magic %08x)\n", im->path, be32(mh)); exit(2); }
    im->mh = mh;
    if (be32(mh + 4) != 18) { LOG("FATAL: %s bukan cputype PPC\n", im->path); exit(2); }

    const char *slash = strrchr(im->path, '/');
    snprintf(im->short_name, sizeof im->short_name, "%s", slash ? slash + 1 : im->path);

    uint32_t ncmds = be32(mh + 16);
    const uint8_t *p = mh + 28;
    for (uint32_t c = 0; c < ncmds; c++) {
        uint32_t cmd = be32(p), size = be32(p + 4);
        switch (cmd) {
        case 0x1: {                                      /* LC_SEGMENT */
            Seg *s = &im->segs[im->nsegs++];
            memcpy(s->name, p + 8, 16); s->name[16] = 0;
            s->vmaddr = be32(p + 24); s->vmsize = be32(p + 28);
            s->fileoff = be32(p + 32); s->filesize = be32(p + 36);
            s->prot = be32(p + 44);
            uint32_t ns = be32(p + 48);
            const uint8_t *q = p + 56;
            for (uint32_t i = 0; i < ns && im->nsects < 80; i++, q += 68) {
                Sect *t = &im->sects[im->nsects++];
                memcpy(t->name, q, 16); t->name[16] = 0;
                memcpy(t->seg, q + 16, 16); t->seg[16] = 0;
                t->addr = be32(q + 32); t->size = be32(q + 36); t->off = be32(q + 40);
                t->flags = be32(q + 56); t->res1 = be32(q + 60); t->res2 = be32(q + 64);
            }
            break; }
        case 0x2:                                        /* LC_SYMTAB */
            im->symoff = be32(p + 8); im->nsyms = be32(p + 12);
            im->stroff = be32(p + 16); im->strsize = be32(p + 20);
            break;
        case 0xb:                                        /* LC_DYSYMTAB */
            im->ilocal = be32(p + 8);  im->nlocal = be32(p + 12);
            im->iext = be32(p + 16);   im->next = be32(p + 20);
            im->iundef = be32(p + 24); im->nundef = be32(p + 28);
            im->indoff = be32(p + 56); im->nind = be32(p + 60);
            im->extreloff = be32(p + 64); im->nextrel = be32(p + 68);
            im->locreloff = be32(p + 72); im->nlocrel = be32(p + 76);
            break;
        case 0xc: case 0x80000018: case 0x8000001f: {   /* LOAD / WEAK / REEXPORT dylib */
            if (im->ndeps < 24) {
                uint32_t so = be32(p + 8);
                snprintf(im->deps[im->ndeps++], 600, "%s", (const char *)(p + so));
            }
            break; }
        case 0x5: {                                      /* LC_UNIXTHREAD */
            im->entry = be32(p + 16);                    /* srr0 */
            im->has_entry = 1;
            break; }
        default: break;
        }
        p += size;
    }

    /* slide & region */
    im->slide = is_exe ? 0 : FW_BASE + (uint32_t)(g_nimg - 1 < 0 ? 0 : g_nimg - 1) * FW_STRIDE;
    uint32_t lo = 0xffffffffu, hi = 0;
    for (int i = 0; i < im->nsegs; i++) {
        Seg *s = &im->segs[i];
        if (!strcmp(s->name, "__PAGEZERO") || !strcmp(s->name, "__LINKEDIT") || !s->vmsize) continue;
        if (s->vmaddr < lo) lo = s->vmaddr;
        if (s->vmaddr + s->vmsize > hi) hi = s->vmaddr + s->vmsize;
    }
    lo = (lo + im->slide) & ~(PAGE_SZ - 1);
    hi = (hi + im->slide + PAGE_SZ - 1) & ~(PAGE_SZ - 1);
    im->lo = lo; im->hi = hi;
    im->host = map_region(im->short_name, lo, hi - lo);
    im->rebased = calloc((hi - lo) / 4, 1);

    for (int i = 0; i < im->nsegs; i++) {
        Seg *s = &im->segs[i];
        if (!strcmp(s->name, "__PAGEZERO") || !strcmp(s->name, "__LINKEDIT") || !s->filesize) continue;
        if ((size_t)(mh - im->file) + s->fileoff + s->filesize > im->filesz) { LOG("FATAL: segmen %s di luar file\n", s->name); exit(2); }
        memcpy(im->host + (s->vmaddr + im->slide - lo), mh + s->fileoff, s->filesize);
    }

    /* export + tabel simbol untuk describe() */
    im->syms = calloc(im->nsyms + 1, sizeof(SymRec));
    for (uint32_t i = 0; i < im->nsyms; i++) {
        uint8_t t; uint32_t v;
        const char *nm = sym_name(im, i, &t, NULL, &v);
        if ((t & 0xe0) || (t & 0x0e) != 0x0e) continue;        /* hanya N_SECT, bukan stab */
        im->syms[im->nsymrec].addr = v + im->slide;
        im->syms[im->nsymrec].name = nm;
        im->nsymrec++;
        if (t & 0x01) exp_add(nm, v + im->slide);               /* N_EXT */
    }
    qsort(im->syms, im->nsymrec, sizeof(SymRec), cmp_symrec);

    im->idx = g_nimg;
    g_img[g_nimg++] = im;
    return im;
}

static int is_system_lib(const char *s)
{
    return !strncmp(s, "/System/", 8) || !strncmp(s, "/usr/lib/", 9);
}

static void load_tree(Image *im)
{
    for (int i = 0; i < im->ndeps; i++) {
        const char *d = im->deps[i];
        if (is_system_lib(d)) continue;
        if (find_loaded(d)) continue;
        Image *c = load_image(d, 0);
        load_tree(c);
    }
    g_order[g_norder++] = im;                                  /* post-order */
}

/* --------------------------------------------------------- HLE: simbol */
typedef uint32_t (*hle_fn)(uint32_t *a);
typedef struct {
    char name[100];
    hle_fn fn;
    uint32_t addr;
    int is_data, known;
    uint64_t calls;
} Hle;
static Hle *g_hle;
static int g_nhle, g_caphle;
static uint32_t g_data_ptr = DATA_BASE + 0x100;
static uint32_t g_trap_slots = 1;                              /* slot 0 = sentinel */

typedef struct { const char *name; hle_fn fn; } HleDef;
static const HleDef *hle_def_find(const char *name);           /* didefinisikan setelah tabel */

static Hle *hle_find(const char *name)
{
    for (int i = 0; i < g_nhle; i++)
        if (!strcmp(g_hle[i].name, name)) return &g_hle[i];
    return NULL;
}

static uint32_t data_alloc(uint32_t n)
{
    uint32_t a = g_data_ptr;
    g_data_ptr += (n + 15) & ~15u;
    if (g_data_ptr > DATA_BASE + DATA_SIZE) { LOG("FATAL: region data HLE penuh\n"); exit(2); }
    return a;
}


/* ---- tabel karakter ala Darwin (isalpha dll. dibaca game langsung dari memori) ---- */
static uint32_t rune_flags(uint32_t c)
{
    if (c >= 128) return 0;
    uint32_t f = 0;
    if (isalpha((int)c))  f |= 0x100;
    if (iscntrl((int)c))  f |= 0x200;
    if (isdigit((int)c))  f |= 0x400;
    if (isgraph((int)c))  f |= 0x800;
    if (islower((int)c))  f |= 0x1000;
    if (ispunct((int)c))  f |= 0x2000;
    if (isspace((int)c))  f |= 0x4000;
    if (isupper((int)c))  f |= 0x8000;
    if (isxdigit((int)c)) f |= 0x10000;
    if (c == ' ' || c == '\t') f |= 0x20000;
    if (isprint((int)c))  f |= 0x40000;
    return f;
}
static uint32_t g_rune_tbl;
static uint32_t rune_table(void)
{
    if (g_rune_tbl) return g_rune_tbl;
    g_rune_tbl = data_alloc(0x1000);
    uint8_t *t = g2h(g_rune_tbl, 0x1000);
    if (!t) return g_rune_tbl;
    memcpy(t, "RuneMagA", 8);
    memcpy(t + 8, "NONE", 5);
    for (uint32_t i = 0; i < 256; i++) {
        wbe32(t + 52 + i * 4, rune_flags(i));
        wbe32(t + 52 + 1024 + i * 4, i < 128 ? (uint32_t)tolower((int)i) : i);
        wbe32(t + 52 + 2048 + i * 4, i < 128 ? (uint32_t)toupper((int)i) : i);
    }
    return g_rune_tbl;
}

static uint32_t hle_symbol(const char *name, int want_data)
{
    Hle *h = hle_find(name);
    if (h) {
        return h->addr;
    }
    if (g_nhle == g_caphle) {
        g_caphle = g_caphle ? g_caphle * 2 : 512;
        g_hle = realloc(g_hle, g_caphle * sizeof(Hle));
    }
    h = &g_hle[g_nhle++];
    memset(h, 0, sizeof *h);
    snprintf(h->name, sizeof h->name, "%s", name);
    const HleDef *def = hle_def_find(name);
    h->fn = def ? def->fn : NULL;
    h->known = def != NULL;
    if (h->known) want_data = 0;
    h->is_data = want_data;
    if (want_data) {
        if (!strcmp(name, "__CurrentRuneLocale")) {
            h->addr = data_alloc(16);
            uint32_t tb = rune_table();
            uint8_t *pp = g2h(h->addr, 4);
            if (pp) wbe32(pp, tb);
        } else if (!strcmp(name, "__DefaultRuneLocale")) {
            h->addr = rune_table();
        } else {
            uint32_t sz = 256;
            if (!strcmp(name, "___sF")) sz = 0x400;
            h->addr = data_alloc(sz);
        }
    } else {
        if (g_trap_slots * 16 >= TRAP_SIZE) { LOG("FATAL: trap slot habis\n"); exit(2); }
        h->addr = TRAP_BASE + g_trap_slots++ * 16;
        uint8_t *s = g2h(h->addr, 16);
        if (s) { wbe32(s, 0x4e800020); }                       /* blr */
    }
    return h->addr;
}

/* ------------------------------------------------- resolusi + relokasi */
enum { CTX_LAZY, CTX_NONLAZY, CTX_EXTREL };

static uint32_t resolve_symbol(Image *im, uint32_t symidx, int ctx)
{
    uint8_t t; uint16_t d; uint32_t v;
    const char *name = sym_name(im, symidx, &t, &d, &v);
    if ((t & 0x0e) == 0x0e) return v + im->slide;                  /* didefinisikan di image ini */
    uint32_t a;
    if (exp_find(name, &a)) return a;                               /* di framework lain */
    if (!strncmp(name, ".objc_class_name_", 17)) return hle_symbol(name, 1);
    if (d & 0x40) return 0;                                         /* N_WEAK_REF */
    return hle_symbol(name, ctx == CTX_EXTREL ? 1 : (ctx == CTX_NONLAZY ? -1 : 0));
}

static void fixup_image(Image *im)
{
    uint8_t *mh = (uint8_t *)im->mh;
    uint32_t base = im->segs[0].vmaddr + im->slide;
#define LOC(addr) g2h((addr), 4)

    /* 1) relokasi lokal (rebase) */
    if (im->slide) {
        for (uint32_t i = 0; i < im->nlocrel; i++) {
            const uint8_t *r = mh + im->locreloff + i * 8;
            uint32_t w0 = be32(r), w1 = be32(r + 4);
            uint32_t addr, type, len;
            if (w0 & 0x80000000u) { addr = w0 & 0xffffff; type = (w0 >> 24) & 0xf; len = (w0 >> 28) & 3; }
            else { addr = w0; type = w1 & 0xf; len = (w1 >> 5) & 3; }
            if ((w0 & 0x80000000u) && type == 9) continue;   /* PPC_RELOC_PB_LA_PTR: pointer malas, ditimpa saat bind */
            if (type != 0 || len != 2) { im->n_odd_reloc++; continue; }
            uint8_t *loc = LOC(base + addr);
            if (!loc) { im->n_odd_reloc++; continue; }
            wbe32(loc, be32(loc) + im->slide);
            im->rebased[(base + addr - im->lo) / 4] = 1;
            im->n_rebase++;
        }
    }
    /* 2) relokasi eksternal (referensi data ke simbol impor) */
    for (uint32_t i = 0; i < im->nextrel; i++) {
        const uint8_t *r = mh + im->extreloff + i * 8;
        uint32_t addr = be32(r), w = be32(r + 4);
        uint32_t symnum = w >> 8, ext = (w >> 4) & 1, len = (w >> 5) & 3, type = w & 0xf;
        if (!ext || len != 2 || type != 0) { im->n_odd_reloc++; continue; }
        uint8_t *loc = LOC(base + addr);
        if (!loc) { im->n_odd_reloc++; continue; }
        uint32_t addend = be32(loc);
        if (addend) im->n_extrel_addend++;
        wbe32(loc, resolve_symbol(im, symnum, CTX_EXTREL) + addend);
        im->n_extrel++;
    }
    /* 3) pointer simbol malas / non-malas lewat indirect symbol table */
    for (int s = 0; s < im->nsects; s++) {
        Sect *t = &im->sects[s];
        uint32_t type = t->flags & 0xff;
        if (type != 6 && type != 7) continue;
        uint32_t n = t->size / 4;
        for (uint32_t k = 0; k < n; k++) {
            uint32_t ind = be32(im->mh + im->indoff + (t->res1 + k) * 4);
            uint32_t pa = t->addr + im->slide + k * 4;
            uint8_t *loc = LOC(pa);
            if (!loc) continue;
            if (ind == 0x80000000u || ind == (0x80000000u | 0x40000000u) || ind == 0x40000000u) {
                /* LOCAL / ABS: pointer ke simbol lokal.  Tambah slide jika belum ter-rebase. */
                if (ind != 0x40000000u && im->slide && !im->rebased[(pa - im->lo) / 4]) {
                    uint32_t v = be32(loc);
                    if (v) { wbe32(loc, v + im->slide); im->n_nl_local++; }
                }
                continue;
            }
            const char *nm = sym_name(im, ind, NULL, NULL, NULL);
            (void)nm;
            uint32_t addr = resolve_symbol(im, ind, type == 7 ? CTX_LAZY : CTX_NONLAZY);
            wbe32(loc, addr);
            if (type == 7) im->n_lazy++; else im->n_nonlazy++;
        }
    }
}

/* -------------------------------------------------- statistik simbol HLE */
static void print_hle_summary(void)
{
    int with = 0, generic = 0, data = 0, cpp = 0;
    for (int i = 0; i < g_nhle; i++) {
        if (g_hle[i].is_data) data++;
        else if (g_hle[i].known) with++;
        else { generic++; if (!strncmp(g_hle[i].name, "__Z", 3)) cpp++; }
    }
    LOG("\n== Ringkasan simbol impor sistem ==\n");
    LOG("total %d  | punya handler: %d | data blob: %d | belum diimplementasi (generik): %d (di antaranya C++ '__Z*': %d)\n",
        g_nhle, with, data, generic, cpp);
}

static void print_unimplemented(void)
{
    LOG("\n== Daftar simbol BELUM diimplementasi (fungsi) ==\n");
    for (int i = 0; i < g_nhle; i++)
        if (!g_hle[i].is_data && !g_hle[i].known) LOG("  %s%s\n", g_hle[i].name, g_hle[i].calls ? "  [DIPANGGIL]" : "");
    LOG("\n== Tabel alamat trap fungsi ==\n");
    for (int i = 0; i < g_nhle; i++)
        if (!g_hle[i].is_data) LOG("  %08x %s\n", g_hle[i].addr, g_hle[i].name);
    LOG("\n== Data blob ==\n");
    for (int i = 0; i < g_nhle; i++)
        if (g_hle[i].is_data) LOG("  %s @%08x\n", g_hle[i].name, g_hle[i].addr);
}

/* ---------------------------------------------------------------- heap */
static uint32_t g_heap_ptr = HEAP_BASE + 0x1000;
static uint32_t heap_alloc(uint32_t n)
{
    uint32_t sz = (n + 15) & ~15u;
    if (g_heap_ptr + 16 + sz > HEAP_BASE + HEAP_SIZE) return 0;
    uint32_t h = g_heap_ptr;
    uint8_t *p = g2h(h, 16);
    wbe32(p, n);
    g_heap_ptr += 16 + sz;
    return h + 16;
}
static uint32_t heap_size(uint32_t a)
{
    uint8_t *p = g2h(a - 16, 16);
    return p ? be32(p) : 0;
}

/* ============================================================ EMULASI */
/* diagnostik crash: jejak blok guest terakhir + HLE terakhir */
static volatile uint32_t g_lastblk[64];
static volatile unsigned g_blkpos;
static const char *volatile g_lasthle;
static volatile int g_curframe = -1;
static int g_blocktrace = 1;
static volatile uint32_t g_lastins[256];
static volatile unsigned g_inspos;
static int g_insntrace = 0;
static int g_stop;
static const char *g_stop_reason = "";
static int g_trace = 0;
static int g_tcg_mb = 32;        /* ukuran buffer JIT (MB); bisa diubah dengan --tcg-mb N */

#ifndef DRYRUN
static uint32_t R(int i)
{
    uint32_t v = 0;
    uc_reg_read(g_uc, UC_PPC_REG_0 + i, &v);
    return v;
}
static void W(int i, uint32_t v) { uc_reg_write(g_uc, UC_PPC_REG_0 + i, &v); }
static uint32_t RLR(void) { uint32_t v = 0; uc_reg_read(g_uc, UC_PPC_REG_LR, &v); return v; }
static uint32_t RPC(void) { uint32_t v = 0; uc_reg_read(g_uc, UC_PPC_REG_PC, &v); return v; }
static void WPC(uint32_t v) { uc_reg_write(g_uc, UC_PPC_REG_PC, &v); }
static void WLR(uint32_t v) { uc_reg_write(g_uc, UC_PPC_REG_LR, &v); }

static void backtrace(void)
{
    uint32_t sp = R(1);
    LOG("  backtrace (dari LR, lalu rantai stack):\n");
    LOG("    LR  = %s\n", describe(RLR()));
    for (int i = 0; i < 12; i++) {
        uint8_t *fr = g2h(sp, 12);
        if (!fr) break;
        uint32_t back = be32(fr), lr = be32(fr + 8);
        if (!back || back <= sp) break;
        LOG("    #%d  = %s\n", i, describe(lr));
        sp = back;
    }
}

static void dump_state(const char *why)
{
    LOG("\n!! BERHENTI: %s\n", why);
    uint32_t pc = RPC();
    LOG("  PC=%s\n", describe(pc));
    for (int i = 0; i < 32; i += 4)
        LOG("  r%-2d=%08x r%-2d=%08x r%-2d=%08x r%-2d=%08x\n", i, R(i), i + 1, R(i + 1), i + 2, R(i + 2), i + 3, R(i + 3));
    uint8_t *b = g2h(pc, 16);
    if (b) LOG("  byte di PC: %02x%02x%02x%02x %02x%02x%02x%02x\n", b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
    {
        uint8_t *pb = g2h(pc - 4, 4);
        if (pb && be32(pb) == 0x44000002) {
            LOG("  instruksi sebelum PC adalah 'sc' (syscall): r0=%u r3=%08x r4=%08x r5=%08x\n", R(0), R(3), R(4), R(5));
            if (R(0) == 4) LOG("  -> write(fd=%u): \"%s\"\n", R(3), gstr(R(4)));
            if (R(0) == 1) LOG("  -> exit(%u)\n", R(3));
        }
    }
    backtrace();
}

#else
static uint32_t R(int i) { (void)i; return 0; }
static void W(int i, uint32_t v) { (void)i; (void)v; }
#endif

/* ============================================================ HLE */
static char g_app_path[700];
static char g_appdata[700];
static uint32_t g_errno_addr, g_fake_obj, g_cstr_c;
static uint32_t g_keymgr[64], g_keymgr_thr[64];
static int g_use_r4;
static uint32_t g_r4;
static double g_t0;

static double mono_s(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

static void hle_state_init(void)
{
    g_errno_addr = data_alloc(16);
    g_fake_obj = data_alloc(128);
    g_cstr_c = data_alloc(16);
    uint8_t *p = g2h(g_cstr_c, 2);
    if (p) { p[0] = 'C'; p[1] = 0; }
    g_t0 = mono_s();
}

/* ---- printf ala Darwin PPC: argumen varargs dibaca dari r3..r10 lalu stack ---- */
typedef struct { int mode; uint32_t k; uint32_t ap; } VaCtx;
static uint32_t va_next(VaCtx *c)
{
    uint32_t v = 0;
    if (c->mode == 0) {
        if (c->k < 8) v = R(3 + (int)c->k);
        else { uint8_t *p = g2h(R(1) + 24 + 4 * c->k, 4); v = p ? be32(p) : 0; }
        c->k++;
    } else {
        uint8_t *p = g2h(c->ap, 4);
        v = p ? be32(p) : 0;
        c->ap += 4;
    }
    return v;
}

static size_t guest_format(char *out, size_t cap, const char *fmt, VaCtx *c)
{
    size_t n = 0;
#define PUT(ch) do { if (n + 1 < cap) out[n] = (char)(ch); n++; } while (0)
    for (const char *f = fmt; *f; f++) {
        if (*f != '%') { PUT(*f); continue; }
        f++;
        if (*f == '%') { PUT('%'); continue; }
        char spec[40];
        int sp = 0;
        spec[sp++] = '%';
        while (*f && strchr("-+ #0", *f) && sp < 8) spec[sp++] = *f++;
        if (*f == '*') { int w = (int)va_next(c); sp += snprintf(spec + sp, 12, "%d", w); f++; }
        else while (*f >= '0' && *f <= '9' && sp < 16) spec[sp++] = *f++;
        if (*f == '.') {
            spec[sp++] = '.'; f++;
            if (*f == '*') { int pv = (int)va_next(c); sp += snprintf(spec + sp, 12, "%d", pv); f++; }
            else while (*f >= '0' && *f <= '9' && sp < 28) spec[sp++] = *f++;
        }
        int lcount = 0;
        while (*f == 'l' || *f == 'h' || *f == 'z' || *f == 't' || *f == 'j' || *f == 'L' || *f == 'q') {
            if (*f == 'l' || *f == 'q' || *f == 'j' || *f == 'L') lcount++;
            f++;
        }
        char conv = *f;
        if (!conv) break;
        spec[sp] = 0;
        char tmp[1100];
        int tl = 0;
        switch (conv) {
        case 'd': case 'i': {
            if (lcount >= 2) {
                uint32_t hi = va_next(c), lo = va_next(c);
                long long v = (long long)(((uint64_t)hi << 32) | lo);
                strcat(spec, "lld");
                tl = snprintf(tmp, sizeof tmp, spec, v);
            } else {
                int v = (int)va_next(c);
                strcat(spec, "d");
                tl = snprintf(tmp, sizeof tmp, spec, v);
            }
            break; }
        case 'u': case 'x': case 'X': case 'o': {
            char suf[4] = { 0, 0, 0, 0 };
            if (lcount >= 2) {
                uint32_t hi = va_next(c), lo = va_next(c);
                unsigned long long v = ((uint64_t)hi << 32) | lo;
                suf[0] = 'l'; suf[1] = 'l'; suf[2] = conv;
                strcat(spec, suf);
                tl = snprintf(tmp, sizeof tmp, spec, v);
            } else {
                unsigned v = va_next(c);
                suf[0] = conv;
                strcat(spec, suf);
                tl = snprintf(tmp, sizeof tmp, spec, v);
            }
            break; }
        case 'c': {
            int v = (int)va_next(c);
            strcat(spec, "c");
            tl = snprintf(tmp, sizeof tmp, spec, v);
            break; }
        case 's': {
            uint32_t p = va_next(c);
            const char *sv = p ? (const char *)g2h(p, 1) : "(null)";
            if (!sv) sv = "(?)";
            strcat(spec, "s");
            tl = snprintf(tmp, sizeof tmp, spec, sv);
            break; }
        case 'p': {
            uint32_t v = va_next(c);
            tl = snprintf(tmp, sizeof tmp, "0x%x", v);
            break; }
        case 'f': case 'F': case 'e': case 'E': case 'g': case 'G': case 'a': case 'A': {
            uint32_t hi = va_next(c), lo = va_next(c);
            uint64_t bits = ((uint64_t)hi << 32) | lo;
            double d;
            memcpy(&d, &bits, 8);
            char suf[2] = { conv, 0 };
            strcat(spec, suf);
            tl = snprintf(tmp, sizeof tmp, spec, d);
            break; }
        default:
            tl = snprintf(tmp, sizeof tmp, "%%%c", conv);
            break;
        }
        if (tl < 0) tl = 0;
        if (tl >= (int)sizeof tmp) tl = (int)sizeof tmp - 1;
        for (int i = 0; i < tl; i++) PUT(tmp[i]);
    }
    if (cap) out[n < cap ? n : cap - 1] = 0;
#undef PUT
    return n;
}

static uint32_t fmt_to_guest(uint32_t dst, uint32_t size, const char *fmt, VaCtx *c, int has_size)
{
    char buf[4096];
    size_t n = guest_format(buf, sizeof buf, fmt, c);
    if (n >= sizeof buf) n = sizeof buf - 1;
    if (!has_size) size = (uint32_t)n + 1;
    if (size) {
        uint8_t *d = g2h(dst, size);
        if (d) {
            size_t m = n < size - 1 ? n : size - 1;
            memcpy(d, buf, m);
            d[m] = 0;
        }
    }
    return (uint32_t)n;
}


/* ===================== runtime Objective-C minimal (ABI lama / ObjC 1) ===================== */
typedef struct { char name[64]; char super[64]; uint32_t cls; uint32_t isz; } GClass;
static GClass g_gcls[16];
static int g_ngcls;
static uint32_t g_cn_lo, g_cn_hi;       /* rentang string nama kelas (__TEXT,__cstring) */
static uint32_t g_tail;                  /* tail-call: PC diarahkan ke IMP guest */
static int g_boot, g_noboot, g_frames = 120;
static uint32_t g_timer_target, g_timer_sel, g_app_obj;

static uint32_t rd32(uint32_t a) { uint8_t *p = g2h(a, 4); return p ? be32(p) : 0; }
static const char *cs(uint32_t a) { const char *p = (const char *)g2h(a, 1); return p ? p : ""; }

static struct { char s[96]; uint32_t addr; } g_intern[96];
static int g_nintern;
static uint32_t intern(const char *s)
{
    for (int i = 0; i < g_nintern; i++) if (!strcmp(g_intern[i].s, s)) return g_intern[i].addr;
    if (g_nintern >= 96) return 0;
    size_t n = strlen(s) + 1;
    if (n > 96) n = 96;
    uint32_t a = data_alloc((uint32_t)n);
    uint8_t *p = g2h(a, (uint32_t)n);
    if (p) { memcpy(p, s, n); p[n - 1] = 0; }
    snprintf(g_intern[g_nintern].s, 96, "%s", s);
    g_intern[g_nintern].addr = a;
    return g_intern[g_nintern++].addr;
}
static int is_interned(uint32_t a)
{
    for (int i = 0; i < g_nintern; i++) if (g_intern[i].addr == a) return 1;
    return 0;
}

static GClass *find_gclass(const char *n)
{
    for (int i = 0; i < g_ngcls; i++) if (!strcmp(g_gcls[i].name, n)) return &g_gcls[i];
    return NULL;
}

static uint32_t find_imp(uint32_t cls, const char *sel)
{
    uint32_t ml = rd32(cls + 28);                 /* methodLists menunjuk langsung ke daftar method */
    for (int guard = 0; ml && ml != 0xffffffffu && guard < 16; guard++) {
        uint32_t cnt = rd32(ml + 4);
        for (uint32_t i = 0; i < cnt && i < 1024; i++) {
            uint32_t e = ml + 8 + 12 * i;
            if (!strcmp(cs(rd32(e)), sel)) return rd32(e + 8);
        }
        ml = rd32(ml);
    }
    return 0;
}

static void objc_register_classes(Image *ex)
{
    uint32_t mod_a = 0, mod_n = 0;
    for (int si = 0; si < ex->nsects; si++) {
        Sect *t = &ex->sects[si];
        /* nama kelas (dipakai referensi kelas) ada di __TEXT,__cstring pada binary ini */
        if (!strcmp(t->seg, "__TEXT") && !strcmp(t->name, "__cstring")) { g_cn_lo = t->addr + ex->slide; g_cn_hi = g_cn_lo + t->size; }
        if (strcmp(t->seg, "__OBJC")) continue;
        if (!strcmp(t->name, "__module_info")) { mod_a = t->addr + ex->slide; mod_n = t->size / 16; }
    }
    for (uint32_t m = 0; m < mod_n; m++) {
        uint32_t st = rd32(mod_a + m * 16 + 12);
        if (!st) continue;
        uint32_t cc = rd32(st + 8) >> 16;
        for (uint32_t i = 0; i < cc && g_ngcls < 16; i++) {
            uint32_t c = rd32(st + 12 + 4 * i);
            GClass *g = &g_gcls[g_ngcls++];
            snprintf(g->name, sizeof g->name, "%s", cs(rd32(c + 8)));
            snprintf(g->super, sizeof g->super, "%s", cs(rd32(c + 4)));
            g->cls = c;
            g->isz = rd32(c + 20);
            LOG("  ObjC kelas: %s : %s (instance %u byte)\n", g->name, g->super, g->isz);
            uint32_t ml = rd32(c + 28);
            for (int guard = 0; ml && ml != 0xffffffffu && guard < 16; guard++) {
                uint32_t cnt = rd32(ml + 4);
                for (uint32_t k = 0; k < cnt && k < 64; k++) {
                    uint32_t e = ml + 8 + 12 * k;
                    LOG("      - %s  imp=%08x\n", cs(rd32(e)), rd32(e + 8));
                }
                ml = rd32(ml);
            }
        }
    }
}

static uint32_t new_obj_guest(GClass *g)
{
    uint32_t sz = g->isz < 16 ? 16 : g->isz;
    uint32_t o = heap_alloc(sz);
    uint8_t *p = g2h(o, 4);
    if (p) wbe32(p, g->cls);
    return o;
}
static uint32_t new_obj_sys(const char *cn)
{
    uint32_t o = heap_alloc(64);
    uint8_t *p = g2h(o, 4);
    if (p) wbe32(p, intern(cn));
    return o;
}
static uint32_t nsstr(const char *str)
{
    uint32_t o = new_obj_sys("NSString");
    uint32_t n = (uint32_t)strlen(str) + 1;
    uint32_t b = heap_alloc(n);
    char *d = (char *)g2h(b, n);
    if (d) memcpy(d, str, n);
    uint8_t *p = g2h(o + 4, 4);
    if (p) wbe32(p, b);
    return o;
}
static const char *nsstr_c(uint32_t o) { return o ? cs(rd32(o + 4)) : ""; }

static struct { char n[32]; uint32_t o; } g_single[8];
static uint32_t singleton(const char *cn)
{
    for (int i = 0; i < 8; i++) {
        if (g_single[i].o && !strcmp(g_single[i].n, cn)) return g_single[i].o;
        if (!g_single[i].o) { snprintf(g_single[i].n, 32, "%s", cn); g_single[i].o = new_obj_sys(cn); return g_single[i].o; }
    }
    return 0;
}

static uint32_t the_app(GClass *gc)
{
    if (!g_app_obj) {
        GClass *g = gc ? gc : find_gclass("LuxorApplication");
        g_app_obj = g ? new_obj_guest(g) : new_obj_sys("NSApplication");
        Hle *h = hle_find("_NSApp");
        if (h) { uint8_t *p = g2h(h->addr, 4); if (p) wbe32(p, g_app_obj); }
        LOG("    NSApp dibuat: %08x\n", g_app_obj);
    }
    return g_app_obj;
}

static char *g_seen[2048];
static int g_nseen;
static int seen_first(const char *k)
{
    if (g_nseen > 1500) return 0;
    uint32_t h = hash_str(k) & 2047;
    while (g_seen[h]) { if (!strcmp(g_seen[h], k)) return 0; h = (h + 1) & 2047; }
    g_seen[h] = strdup(k);
    g_nseen++;
    return 1;
}

typedef struct { int valid, is_class; GClass *gc; char name[64]; } Recv;
static Recv classify(uint32_t self)
{
    Recv r;
    memset(&r, 0, sizeof r);
    if (!self) return r;
    if (self >= g_cn_lo && self < g_cn_hi) {            /* referensi kelas = penunjuk ke nama kelas */
        snprintf(r.name, sizeof r.name, "%s", cs(self));
        r.is_class = 1; r.valid = 1; r.gc = find_gclass(r.name);
        return r;
    }
    uint32_t isa = rd32(self);
    for (int i = 0; i < g_ngcls; i++)
        if (g_gcls[i].cls == isa) {
            r.gc = &g_gcls[i]; snprintf(r.name, sizeof r.name, "%s", g_gcls[i].name); r.valid = 1;
            return r;
        }
    if (is_interned(isa)) { snprintf(r.name, sizeof r.name, "%s", cs(isa)); r.valid = 1; }
    return r;
}

static uint32_t sys_msg(const char *cn, int is_class, GClass *gc, uint32_t self, const char *sel, uint32_t *a)
{
    char key[220];
    snprintf(key, sizeof key, "%c[%s %s]", is_class ? '+' : '-', cn, sel);
    if (seen_first(key)) LOG("    objc: %s\n", key);
    if (is_class) {
        if (!strcmp(sel, "alloc") || !strcmp(sel, "allocWithZone:") || !strcmp(sel, "new"))
            return gc ? new_obj_guest(gc) : new_obj_sys(cn);
        if (!strcmp(sel, "sharedApplication")) return the_app(gc);
        if (!strcmp(cn, "NSBundle") && !strcmp(sel, "mainBundle")) return singleton("NSBundle");
        if (!strcmp(cn, "NSFileManager") && !strcmp(sel, "defaultManager")) return singleton("NSFileManager");
        if (!strcmp(cn, "NSString") && (!strcmp(sel, "stringWithUTF8String:") || !strncmp(sel, "stringWithCString:", 18)))
            return nsstr(cs(a[2]));
        if (!strcmp(cn, "NSTimer") && !strncmp(sel, "scheduledTimerWithTimeInterval:target:selector:", 47)) {
            g_timer_target = a[4];          /* double memakai slot r5:r6 */
            g_timer_sel = a[5];
            LOG("    NSTimer terdaftar: target=%08x selector=\"%s\"\n", a[4], cs(a[5]));
            return new_obj_sys("NSTimer");
        }
        return 0;
    }
    if (!strncmp(sel, "init", 4) || !strcmp(sel, "retain") || !strcmp(sel, "autorelease") ||
        !strcmp(sel, "self") || !strcmp(sel, "copy"))
        return self;
    if (!strcmp(cn, "NSBundle")) {
        char b[800];
        if (!strcmp(sel, "resourcePath")) { snprintf(b, sizeof b, "%s/Contents/Resources", g_app_path); return nsstr(b); }
        if (!strcmp(sel, "bundlePath")) return nsstr(g_app_path);
        if (!strcmp(sel, "executablePath")) { snprintf(b, sizeof b, "%s/Contents/MacOS/Luxor", g_app_path); return nsstr(b); }
    }
    if (!strcmp(cn, "NSString")) {
        if (!strcmp(sel, "cString") || !strcmp(sel, "UTF8String") || !strcmp(sel, "lossyCString") ||
            !strcmp(sel, "fileSystemRepresentation"))
            return rd32(self + 4);
        if (!strcmp(sel, "length")) return (uint32_t)strlen(nsstr_c(self));
        if (!strcmp(sel, "stringByAppendingString:") || !strcmp(sel, "stringByAppendingPathComponent:")) {
            char b[1600];
            snprintf(b, sizeof b, "%s%s%s", nsstr_c(self), sel[16] == 'P' ? "/" : "", nsstr_c(a[2]));
            return nsstr(b);
        }
        if (!strcmp(sel, "isEqualToString:")) return strcmp(nsstr_c(self), nsstr_c(a[2])) == 0;
    }
    if (!strcmp(cn, "NSFileManager")) {
        if (!strcmp(sel, "changeCurrentDirectoryPath:")) {
            int r = chdir(nsstr_c(a[2]));
            LOG("    chdir(\"%s\") -> %d\n", nsstr_c(a[2]), r);
            return r == 0;
        }
        if (!strcmp(sel, "currentDirectoryPath")) { char b[800]; if (!getcwd(b, sizeof b)) b[0] = 0; return nsstr(b); }
    }
    return 0;
}

static uint32_t do_msg(uint32_t self, uint32_t sel, uint32_t *a)
{
    const char *selname = cs(sel);
    Recv r = classify(self);
    if (!r.valid) {
        if (self) {
            char k[64];
            snprintf(k, sizeof k, "?recv %08x", self);
            if (seen_first(k)) LOG("    objc: penerima tak dikenal %08x sel=%s (isa=%08x)\n", self, selname, rd32(self));
        }
        return 0;
    }
    if (!r.is_class) {
        for (GClass *g = r.gc; g; g = find_gclass(g->super)) {
            uint32_t imp = find_imp(g->cls, selname);
            if (imp) { g_tail = imp; return 0; }
        }
    }
    const char *cn = r.name;
    for (GClass *g = r.gc; g; g = find_gclass(g->super)) cn = g->super;   /* naik ke kelas sistem teratas */
    return sys_msg(cn, r.is_class, r.gc, self, selname, a);
}


static int cmp_calls(const void *x, const void *y)
{
    const Hle *p = &g_hle[*(const int *)x], *q = &g_hle[*(const int *)y];
    return (p->calls < q->calls) - (p->calls > q->calls);
}
static void print_call_stats(void)
{
    int idx[1024], n = 0;
    for (int i = 0; i < g_nhle && n < 1024; i++) if (g_hle[i].calls) idx[n++] = i;
    qsort(idx, n, sizeof(int), cmp_calls);
    LOG("\nheap guest terpakai: %u KB dari %u KB\n", (unsigned)((g_heap_ptr - HEAP_BASE) / 1024), (unsigned)(HEAP_SIZE / 1024));
    LOG("\n== Statistik panggilan HLE (terbanyak) ==\n");
    for (int i = 0; i < n && i < 80; i++)
        LOG("  %8llu  %s%s\n", (unsigned long long)g_hle[idx[i]].calls, g_hle[idx[i]].name, g_hle[idx[i]].known ? "" : "  [generik]");
}

/* ===================== I/O file berbasis FILE* host ===================== */
static FILE *g_fp[64];
static uint32_t g_fpaddr[64];
static int g_nfopen;
static uint32_t file_new(FILE *f)
{
    for (int i = 3; i < 64; i++)
        if (!g_fp[i]) {
            g_fp[i] = f;
            if (!g_fpaddr[i]) g_fpaddr[i] = data_alloc(16);
            uint8_t *p = g2h(g_fpaddr[i], 4);
            if (p) wbe32(p, (uint32_t)i);
            return g_fpaddr[i];
        }
    fclose(f);
    return 0;
}
static FILE *file_get(uint32_t a)
{
    for (int i = 3; i < 64; i++) if (g_fp[i] && g_fpaddr[i] == a) return g_fp[i];
    return NULL;
}
static void file_drop(uint32_t a)
{
    for (int i = 3; i < 64; i++) if (g_fp[i] && g_fpaddr[i] == a) { fclose(g_fp[i]); g_fp[i] = NULL; }
}

/* ===================== register floating point (untuk fungsi math) ===================== */
#if !defined(DRYRUN) && defined(LUXOR_HAVE_FPR)
static double F(int i)
{
    uint64_t v = 0; double d;
    uc_reg_read(g_uc, UC_PPC_REG_FPR0 + i, &v);
    memcpy(&d, &v, 8);
    return d;
}
static void SF(int i, double d)
{
    uint64_t v;
    memcpy(&v, &d, 8);
    uc_reg_write(g_uc, UC_PPC_REG_FPR0 + i, &v);
}
#else
static double F(int i) { (void)i; return 0; }
static void SF(int i, double d) { (void)i; (void)d; }
#endif

#define H(n) static uint32_t n(uint32_t *a)
#define UNUSED (void)a

H(h_malloc)  { return heap_alloc(a[0]); }
H(h_calloc)  { return heap_alloc(a[0] * a[1]); }
H(h_free)    { UNUSED; return 0; }
H(h_realloc) {
    if (!a[0]) return heap_alloc(a[1]);
    uint32_t old = heap_size(a[0]), n = heap_alloc(a[1]);
    if (!n) return 0;
    uint32_t c = old < a[1] ? old : a[1];
    uint8_t *s = g2h(a[0], c), *d = g2h(n, c);
    if (s && d) memmove(d, s, c);
    return n;
}
H(h_memcpy)  { uint8_t *d = g2h(a[0], a[2]), *s = g2h(a[1], a[2]); if (d && s) memmove(d, s, a[2]); return a[0]; }
H(h_memset)  { uint8_t *d = g2h(a[0], a[2]); if (d) memset(d, (int)a[1], a[2]); return a[0]; }
H(h_memcmp)  { uint8_t *d = g2h(a[0], a[2]), *s = g2h(a[1], a[2]); return (d && s) ? (uint32_t)memcmp(d, s, a[2]) : 0; }
H(h_memchr)  { uint8_t *s = g2h(a[0], a[2]); if (!s) return 0; void *r = memchr(s, (int)a[1], a[2]); return r ? a[0] + (uint32_t)((uint8_t *)r - s) : 0; }
H(h_strlen)  { const uint8_t *s = g2h(a[0], 1); return s ? (uint32_t)strlen((const char *)s) : 0; }
H(h_strcmp)  { const uint8_t *x = g2h(a[0], 1), *y = g2h(a[1], 1); return (x && y) ? (uint32_t)strcmp((const char *)x, (const char *)y) : 0; }
H(h_strncmp) { const uint8_t *x = g2h(a[0], 1), *y = g2h(a[1], 1); return (x && y) ? (uint32_t)strncmp((const char *)x, (const char *)y, a[2]) : 0; }
H(h_strcpy)  { const uint8_t *s = g2h(a[1], 1); if (s) { size_t n = strlen((const char *)s) + 1; uint8_t *d = g2h(a[0], n); if (d) memmove(d, s, n); } return a[0]; }
H(h_strncpy) { uint8_t *d = g2h(a[0], a[2]); const uint8_t *s = g2h(a[1], 1); if (d && s) strncpy((char *)d, (const char *)s, a[2]); return a[0]; }
H(h_strcat)  {
    const char *s = (const char *)g2h(a[1], 1), *d0 = (const char *)g2h(a[0], 1);
    if (s && d0) { size_t dl = strlen(d0), sl = strlen(s); char *d = (char *)g2h(a[0], dl + sl + 1); if (d) memmove(d + dl, s, sl + 1); }
    return a[0];
}
H(h_strncat) {
    const char *s = (const char *)g2h(a[1], 1), *d0 = (const char *)g2h(a[0], 1);
    if (s && d0) { size_t dl = strlen(d0), sl = strnlen(s, a[2]); char *d = (char *)g2h(a[0], dl + sl + 1); if (d) { memmove(d + dl, s, sl); d[dl + sl] = 0; } }
    return a[0];
}
H(h_strdup)  { const char *s = (const char *)g2h(a[0], 1); if (!s) return 0; size_t n = strlen(s) + 1; uint32_t p = heap_alloc((uint32_t)n); char *d = (char *)g2h(p, (uint32_t)n); if (d) memcpy(d, s, n); return p; }
H(h_strchr)  { const uint8_t *s = g2h(a[0], 1); if (!s) return 0; const char *r = strchr((const char *)s, (int)a[1]); return r ? a[0] + (uint32_t)(r - (const char *)s) : 0; }
H(h_strrchr) { const uint8_t *s = g2h(a[0], 1); if (!s) return 0; const char *r = strrchr((const char *)s, (int)a[1]); return r ? a[0] + (uint32_t)(r - (const char *)s) : 0; }
H(h_strstr)  { const char *s = (const char *)g2h(a[0], 1), *t = (const char *)g2h(a[1], 1); if (!s || !t) return 0; const char *r = strstr(s, t); return r ? a[0] + (uint32_t)(r - s) : 0; }
H(h_atoi)    { const char *s = (const char *)g2h(a[0], 1); return s ? (uint32_t)atoi(s) : 0; }
H(h_strtol)  { const char *s = (const char *)g2h(a[0], 1); if (!s) return 0; char *e; long v = strtol(s, &e, (int)a[2]); if (a[1]) { uint8_t *pp = g2h(a[1], 4); if (pp) wbe32(pp, a[0] + (uint32_t)(e - s)); } return (uint32_t)v; }
H(h_strtoul) { const char *s = (const char *)g2h(a[0], 1); if (!s) return 0; char *e; unsigned long v = strtoul(s, &e, (int)a[2]); if (a[1]) { uint8_t *pp = g2h(a[1], 4); if (pp) wbe32(pp, a[0] + (uint32_t)(e - s)); } return (uint32_t)v; }
H(h_strtoq)  { const char *s = (const char *)g2h(a[0], 1); if (!s) return 0; char *e; long long v = strtoll(s, &e, (int)a[2]); if (a[1]) { uint8_t *pp = g2h(a[1], 4); if (pp) wbe32(pp, a[0] + (uint32_t)(e - s)); } g_r4 = (uint32_t)v; g_use_r4 = 1; return (uint32_t)((uint64_t)v >> 32); }
H(h_strtouq) { const char *s = (const char *)g2h(a[0], 1); if (!s) return 0; char *e; unsigned long long v = strtoull(s, &e, (int)a[2]); if (a[1]) { uint8_t *pp = g2h(a[1], 4); if (pp) wbe32(pp, a[0] + (uint32_t)(e - s)); } g_r4 = (uint32_t)v; g_use_r4 = 1; return (uint32_t)(v >> 32); }
H(h_tolower) { return a[0] < 128 ? (uint32_t)tolower((int)a[0]) : a[0]; }
H(h_toupper) { return a[0] < 128 ? (uint32_t)toupper((int)a[0]) : a[0]; }
H(h_istype)  { return (rune_flags(a[0]) & a[1]) ? 1 : 0; }
H(h_maskrune){ return rune_flags(a[0]) & a[1]; }
H(h_runetype){ return rune_flags(a[0]); }
H(h_rand)    { UNUSED; return (uint32_t)(rand() & 0x7fffffff); }
H(h_setlocale){ UNUSED; return g_cstr_c; }
H(h_error)   { UNUSED; return g_errno_addr; }
H(h_zero)    { UNUSED; return 0; }
H(h_one)     { UNUSED; return 1; }
H(h_getenv)  { UNUSED; return 0; }
H(h_abort)   { UNUSED; if (!g_stop) { g_stop = 1; g_stop_reason = "abort() dipanggil oleh game"; } return 0; }
H(h_exit)    { if (!g_stop) { g_stop = 1; g_stop_reason = "exit() dipanggil oleh game"; } LOG("  exit(%d)\n", (int)a[0]); return 0; }
H(h_new)     { return heap_alloc(a[0]); }

H(h_snprintf) { const char *f = (const char *)g2h(a[2], 1); if (!f) return 0; VaCtx c = { 0, 3, 0 }; return fmt_to_guest(a[0], a[1], f, &c, 1); }
H(h_sprintf)  { const char *f = (const char *)g2h(a[1], 1); if (!f) return 0; VaCtx c = { 0, 2, 0 }; return fmt_to_guest(a[0], 0, f, &c, 0); }
H(h_vsnprintf){ const char *f = (const char *)g2h(a[2], 1); if (!f) return 0; VaCtx c = { 1, 0, a[3] }; return fmt_to_guest(a[0], a[1], f, &c, 1); }
H(h_printf)   {
    const char *f = (const char *)g2h(a[0], 1); if (!f) return 0;
    VaCtx c = { 0, 1, 0 }; char buf[2048]; size_t n = guest_format(buf, sizeof buf, f, &c);
    LOG("    [printf] %s%s", buf, (n && buf[n < sizeof buf ? n - 1 : 0] == '\n') ? "" : "\n"); return (uint32_t)n;
}
H(h_fprintf)  {
    const char *f = (const char *)g2h(a[1], 1); if (!f) return 0;
    VaCtx c = { 0, 2, 0 }; char buf[2048]; size_t n = guest_format(buf, sizeof buf, f, &c);
    LOG("    [fprintf] %s%s", buf, (n && buf[n < sizeof buf ? n - 1 : 0] == '\n') ? "" : "\n"); return (uint32_t)n;
}
H(h_puts)    { LOG("    puts: %s\n", gstr(a[0])); return 1; }
H(h_write)   {
    if (a[0] == 1 || a[0] == 2) { uint8_t *b = g2h(a[1], a[2]); if (b) LOG("    write(%u): %.*s\n", a[0], (int)a[2], b); }
    return a[2];
}
H(h_mkdir)   { const char *p = (const char *)g2h(a[0], 1); if (!p) return 0xffffffffu; int r = mkdir(p, 0755); return (r == 0 || errno == EEXIST) ? 0 : 0xffffffffu; }

H(h_msgsend)       { return do_msg(a[0], a[1], a); }
H(h_msgsend_stret) { uint32_t b[8]; for (int k = 0; k < 7; k++) b[k] = a[k + 1]; b[7] = 0; return do_msg(b[0], b[1], b); }
H(h_msgsend_super) {
    uint32_t recv = rd32(a[0]), kl = rd32(a[0] + 4);
    uint32_t b[8];
    memcpy(b, a, sizeof b);
    b[0] = recv;
    W(3, recv);
    const char *selname = cs(a[1]);
    GClass *g = NULL;
    const char *cn = NULL;
    if (kl >= g_cn_lo && kl < g_cn_hi) { cn = cs(kl); g = find_gclass(cn); }
    else for (int i = 0; i < g_ngcls; i++) if (g_gcls[i].cls == kl) { g = &g_gcls[i]; cn = g->name; }
    Recv r = classify(recv);
    for (; g; g = find_gclass(g->super)) {
        uint32_t imp = find_imp(g->cls, selname);
        if (imp) { g_tail = imp; return 0; }
        cn = g->super;
    }
    if (!cn) cn = "NSObject";
    return sys_msg(cn, r.valid ? r.is_class : 0, r.gc, recv, selname, b);
}
H(h_nsappmain) {
    UNUSED;
    if (!g_stop) { g_stop = 1; g_stop_reason = "NSApplicationMain() tercapai (MILESTONE 1) -> lanjut bootstrap M2"; }
    g_boot = 1;
    return 0;
}

/* file */
H(h_fopen) {
    FILE *f = fopen(cs(a[0]), cs(a[1]));
    uint32_t r = f ? file_new(f) : 0;
    if (g_nfopen++ < 80) LOG("    fopen(\"%s\", \"%s\") -> %s\n", cs(a[0]), cs(a[1]), r ? "OK" : "GAGAL");
    return r;
}
H(h_fclose)  { FILE *f = file_get(a[0]); if (f) { file_drop(a[0]); return 0; } return 0xffffffffu; }
H(h_fread)   { FILE *f = file_get(a[3]); uint64_t n = (uint64_t)a[1] * a[2]; if (!f || !n || n > 0x4000000u) return 0; uint8_t *b = g2h(a[0], (uint32_t)n); if (!b) return 0; size_t got = fread(b, a[1], a[2], f); return (uint32_t)got; }
H(h_fwrite)  { FILE *f = file_get(a[3]); uint64_t n = (uint64_t)a[1] * a[2]; if (!f || !n || n > 0x4000000u) return a[2]; uint8_t *b = g2h(a[0], (uint32_t)n); if (!b) return 0; return (uint32_t)fwrite(b, a[1], a[2], f); }
H(h_fseek)   { FILE *f = file_get(a[0]); if (!f) return 0xffffffffu; return (uint32_t)fseek(f, (long)(int32_t)a[1], (int)a[2]); }
H(h_ftell)   { FILE *f = file_get(a[0]); return f ? (uint32_t)ftell(f) : 0xffffffffu; }
H(h_fgets)   { FILE *f = file_get(a[2]); if (!f || !a[1]) return 0; char *b = (char *)g2h(a[0], a[1]); if (!b) return 0; return fgets(b, (int)a[1], f) ? a[0] : 0; }
H(h_getc)    { FILE *f = file_get(a[0]); return f ? (uint32_t)fgetc(f) : 0xffffffffu; }
H(h_ungetc)  { FILE *f = file_get(a[1]); return f ? (uint32_t)ungetc((int)a[0], f) : 0xffffffffu; }
H(h_tmpfile) { UNUSED; FILE *f = tmpfile(); return f ? file_new(f) : 0; }
H(h_chdir)   { int r = chdir(cs(a[0])); LOG("    chdir(\"%s\") -> %d\n", cs(a[0]), r); return r == 0 ? 0 : 0xffffffffu; }

/* math (argumen/hasil double lewat FPR; slot GPR dicadangkan, jadi argumen int sesudah double ada di r5) */
#define MATH1(nm, expr) H(nm) { UNUSED; double x = F(1); SF(1, (expr)); return 0; }
MATH1(h_sin, sin(x))   MATH1(h_cos, cos(x))   MATH1(h_tan, tan(x))   MATH1(h_atan, atan(x))
MATH1(h_acos, acos(x)) MATH1(h_sqrt, sqrt(x)) MATH1(h_floor, floor(x)) MATH1(h_ceil, ceil(x))
MATH1(h_fabs, fabs(x)) MATH1(h_exp, exp(x))   MATH1(h_log, log(x))   MATH1(h_rint, rint(x))
H(h_pow)    { UNUSED; SF(1, pow(F(1), F(2))); return 0; }
H(h_atan2)  { UNUSED; SF(1, atan2(F(1), F(2))); return 0; }
H(h_fmod)   { UNUSED; SF(1, fmod(F(1), F(2))); return 0; }
H(h_ldexp)  { SF(1, ldexp(F(1), (int)a[2])); return 0; }
H(h_frexp)  { int e = 0; double m = frexp(F(1), &e); uint8_t *p = g2h(a[2], 4); if (p) wbe32(p, (uint32_t)e); SF(1, m); return 0; }
H(h_finite) { UNUSED; return isfinite(F(1)) ? 1 : 0; }
H(h_abs)    { int v = (int)a[0]; return (uint32_t)(v < 0 ? -v : v); }
H(h_atof)   { const char *p = cs(a[0]); SF(1, atof(p)); return 0; }
H(h_strtod) { const char *p = cs(a[0]); char *e; double v = strtod(p, &e); if (a[1]) { uint8_t *q = g2h(a[1], 4); if (q) wbe32(q, a[0] + (uint32_t)(e - p)); } SF(1, v); return 0; }


static uint32_t g_tls_key = 1;
static uint32_t g_tls[64];
H(h_key_create) { uint8_t *p = g2h(a[0], 4); if (p) wbe32(p, g_tls_key++); return 0; }
H(h_getspecific) { return a[0] < 64 ? g_tls[a[0]] : 0; }
H(h_setspecific) { if (a[0] < 64) g_tls[a[0]] = a[1]; return 0; }

/* keymgr (dipakai runtime C++ GCC di macOS) */
H(h_km_get)  { return g_keymgr[a[0] & 63]; }
H(h_km_set)  { g_keymgr[a[0] & 63] = a[1]; return 0; }
H(h_kmt_get) { return g_keymgr_thr[a[0] & 63]; }
H(h_kmt_set) { g_keymgr_thr[a[0] & 63] = a[1]; return 0; }

/* dyld */
H(h_dyld_lookup) {
    const char *nm = (const char *)g2h(a[0], 1);
    if (!nm) return 0;
    int existed = hle_find(nm) != NULL;
    uint32_t addr = hle_symbol(nm, 0);
    uint8_t *p = g2h(a[1], 4);
    if (p) wbe32(p, addr);
    if (!existed) LOG("    dyld_func_lookup(\"%s\") -> %08x\n", nm, addr);
    return 1;
}

/* Carbon / CoreFoundation secukupnya */
H(h_getcurproc)  { uint8_t *p = g2h(a[0], 8); if (p) memset(p, 0, 8); return 0; }
H(h_copyprocname){ uint8_t *p = g2h(a[1], 4); if (p) wbe32(p, g_fake_obj); return 0; }
H(h_cfs_getc)    { char *b = (char *)g2h(a[1], a[2] ? a[2] : 1); if (!b || a[2] < 6) return 0; memcpy(b, "Luxor", 6); return 1; }
H(h_fsrefpath)   { char *b = (char *)g2h(a[1], a[2] ? a[2] : 1); if (!b) return 0xffffffffu; snprintf(b, a[2], "%s", g_appdata); return 0; }
H(h_bundle_main) { UNUSED; return g_fake_obj + 0x10; }
H(h_bundle_res)  { UNUSED; return g_fake_obj + 0x20; }
H(h_url_fsrep)   { char *b = (char *)g2h(a[2], a[3] ? a[3] : 1); if (!b) return 0; snprintf(b, a[3], "%s/Contents/Resources", g_app_path); return 1; }
H(h_prefs_valid) { if (a[2]) { uint8_t *p = g2h(a[2], 1); if (p) *p = 0; } return 0; }
H(h_gestalt)     { uint8_t *p = g2h(a[1], 4); if (p) wbe32(p, a[0] == 0x73797376u ? 0x1049u : 0u); return 0; }
H(h_microsec)    { uint8_t *p = g2h(a[0], 8); uint64_t us = (uint64_t)((mono_s() - g_t0) * 1e6); if (p) { wbe32(p, (uint32_t)(us >> 32)); wbe32(p + 4, (uint32_t)us); } return 0; }
H(h_uptime)      { UNUSED; uint64_t ns = (uint64_t)((mono_s() - g_t0) * 1e9); g_r4 = (uint32_t)ns; g_use_r4 = 1; return (uint32_t)(ns >> 32); }
H(h_addns)       { uint64_t s = (((uint64_t)a[0] << 32) | a[1]) + (((uint64_t)a[2] << 32) | a[3]); g_r4 = (uint32_t)s; g_use_r4 = 1; return (uint32_t)(s >> 32); }
H(h_pixw)        { UNUSED; return 640; }
H(h_pixh)        { UNUSED; return 480; }
H(h_bpp)         { UNUSED; return 32; }

static const HleDef g_defs[] = {
    {"_malloc", h_malloc}, {"_calloc", h_calloc}, {"_free", h_free}, {"_realloc", h_realloc},
    {"_valloc", h_malloc}, {"_memalign", h_malloc},
    {"_memcpy", h_memcpy}, {"_memmove", h_memcpy}, {"_memset", h_memset}, {"_memcmp", h_memcmp}, {"_memchr", h_memchr},
    {"_bcopy", h_zero},
    {"_strlen", h_strlen}, {"_strcmp", h_strcmp}, {"_strncmp", h_strncmp},
    {"_strcpy", h_strcpy}, {"_strncpy", h_strncpy}, {"_strcat", h_strcat}, {"_strncat", h_strncat},
    {"_strdup", h_strdup}, {"_strchr", h_strchr}, {"_strrchr", h_strrchr}, {"_strstr", h_strstr},
    {"_atoi", h_atoi}, {"_strtol", h_strtol}, {"_strtoul", h_strtoul}, {"_strtoq", h_strtoq}, {"_strtouq", h_strtouq},
    {"_tolower", h_tolower}, {"_toupper", h_toupper}, {"____tolower", h_tolower}, {"____toupper", h_toupper},
    {"___istype", h_istype}, {"___maskrune", h_maskrune}, {"____runetype", h_runetype},
    {"_rand", h_rand}, {"_srand", h_zero}, {"_setlocale", h_setlocale}, {"___error", h_error},
    {"_abort", h_abort}, {"_exit", h_exit}, {"__exit", h_exit},
    {"__Znwm", h_new}, {"__Znam", h_new}, {"__ZdlPv", h_free}, {"__ZdaPv", h_free},
    {"_getenv", h_getenv}, {"_atexit", h_zero}, {"___cxa_atexit", h_zero},
    /* __mach_init_routine / __cthread_init_routine adalah VARIABEL (penunjuk fungsi, isi NULL), bukan fungsi */
    {"__dyld_register_func_for_add_image", h_zero}, {"__dyld_register_func_for_remove_image", h_zero},
    {"<dyld_lazy_binder>", h_zero}, {"<dyld_func_lookup>", h_dyld_lookup},
    {"_getpid", h_one}, {"_isatty", h_zero}, {"_chdir", h_chdir},
    {"_pthread_self", h_one}, {"_pthread_mutex_init", h_zero}, {"_pthread_mutex_lock", h_zero},
    {"_pthread_mutex_unlock", h_zero}, {"_pthread_mutex_destroy", h_zero},
    {"_pthread_mutexattr_init", h_zero}, {"_pthread_mutexattr_settype", h_zero},
    {"_pthread_mutexattr_destroy", h_zero}, {"_pthread_cond_init", h_zero},
    {"_pthread_key_create", h_key_create}, {"_pthread_getspecific", h_getspecific},
    {"_pthread_setspecific", h_setspecific},
    {"__init_keymgr", h_zero}, {"___keymgr_dwarf2_register_sections", h_zero},
    {"__keymgr_get_and_lock_processwide_ptr", h_km_get}, {"__keymgr_set_and_unlock_processwide_ptr", h_km_set},
    {"__keymgr_unlock_processwide_ptr", h_zero},
    {"__keymgr_get_per_thread_data", h_kmt_get}, {"__keymgr_set_per_thread_data", h_kmt_set},
    {"_printf", h_printf}, {"_fprintf", h_fprintf}, {"_sprintf", h_sprintf}, {"_snprintf", h_snprintf},
    {"_vsnprintf", h_vsnprintf}, {"_puts", h_puts}, {"_write", h_write}, {"_fopen", h_fopen}, {"_mkdir", h_mkdir},
    {"_syslog", h_zero}, {"_openlog", h_zero}, {"_closelog", h_zero},
    {"_objc_msgSend", h_msgsend}, {"_objc_msgSendSuper", h_msgsend_super}, {"_objc_msgSend_stret", h_msgsend_stret},
    {"_NSApplicationMain", h_nsappmain},
    {"_fclose", h_fclose}, {"_fread", h_fread}, {"_fwrite", h_fwrite}, {"_fseek", h_fseek}, {"_ftell", h_ftell},
    {"_fgets", h_fgets}, {"_getc", h_getc}, {"_ungetc", h_ungetc}, {"_tmpfile", h_tmpfile},
    {"_fflush", h_zero}, {"_setvbuf", h_zero}, {"_fdopen", h_zero}, {"_fcntl", h_zero},
    {"_sin", h_sin}, {"_cos", h_cos}, {"_tan", h_tan}, {"_atan", h_atan}, {"_acos", h_acos}, {"_sqrt", h_sqrt},
    {"_floor", h_floor}, {"_ceil", h_ceil}, {"_fabs", h_fabs}, {"_exp", h_exp}, {"_log", h_log}, {"_rint", h_rint},
    {"_pow", h_pow}, {"_atan2", h_atan2}, {"_fmod", h_fmod}, {"_ldexp", h_ldexp}, {"_frexp", h_frexp},
    {"_finite", h_finite}, {"_abs", h_abs}, {"_atof", h_atof}, {"_strtod", h_strtod},
    {"_FSFindFolder", h_zero}, {"_FSRefMakePath", h_fsrefpath}, {"_GetCurrentProcess", h_getcurproc},
    {"_CopyProcessName", h_copyprocname}, {"_CFStringGetCString", h_cfs_getc}, {"_CFRelease", h_zero},
    {"_CFBundleGetMainBundle", h_bundle_main}, {"_CFBundleCopyResourcesDirectoryURL", h_bundle_res},
    {"_CFURLGetFileSystemRepresentation", h_url_fsrep},
    {"_CFPreferencesGetAppBooleanValue", h_prefs_valid}, {"_CFPreferencesGetAppIntegerValue", h_prefs_valid},
    {"_Gestalt", h_gestalt}, {"_Microseconds", h_microsec}, {"_UpTime", h_uptime},
    {"_AddNanosecondsToAbsolute", h_addns}, {"_MPDelayUntil", h_zero},
    {"_CGDisplayPixelsWide", h_pixw}, {"_CGDisplayPixelsHigh", h_pixh}, {"_CGDisplayBitsPerPixel", h_bpp},
    {NULL, NULL}
};

#ifndef DRYRUN

static void hook_insn(uc_engine *uc, uint64_t address, uint32_t size, void *ud)
{
    (void)uc; (void)size; (void)ud;
    g_lastins[g_inspos++ & 255] = (uint32_t)address;
}

static void hook_block(uc_engine *uc, uint64_t address, uint32_t size, void *ud)
{
    (void)uc; (void)size; (void)ud;
    g_lastblk[g_blkpos++ & 63] = (uint32_t)address;
}

static void crash_handler(int sig)
{
    char buf[6200];
    int n = 0;
    n += snprintf(buf + n, sizeof buf - n, "\n!! SINYAL %d (%s) pada proses loader\n", sig,
                  sig == SIGABRT ? "abort" : sig == SIGSEGV ? "segfault" : sig == SIGBUS ? "bus error" : "lain");
    n += snprintf(buf + n, sizeof buf - n, "   frame=%d  HLE terakhir=%s  heap terpakai=%u KB\n",
                  g_curframe, g_lasthle ? g_lasthle : "-", (unsigned)((g_heap_ptr - HEAP_BASE) / 1024));
    n += snprintf(buf + n, sizeof buf - n, "   blok guest terakhir (terbaru dulu):\n");
    unsigned pos = g_blkpos;
    for (int i = 0; i < 20 && n < (int)sizeof buf - 240; i++) {
        uint32_t a = g_lastblk[(pos - 1 - (unsigned)i) & 63];
        n += snprintf(buf + n, sizeof buf - n, "     %s\n", describe(a));
    }
    if (g_insntrace) {
        n += snprintf(buf + n, sizeof buf - n, "   instruksi guest terakhir (terbaru dulu; alamat: kode  fungsi):\n");
        unsigned ip = g_inspos;
        for (int i = 0; i < 24 && n < (int)sizeof buf - 260; i++) {
            uint32_t a = g_lastins[(ip - 1 - (unsigned)i) & 255];
            n += snprintf(buf + n, sizeof buf - n, "     %08x: %08x  %s\n", a, rd32(a), describe(a));
        }
    }
    if (g_logf) { fwrite(buf, 1, (size_t)n, g_logf); fflush(g_logf); }
    if (write(1, buf, (size_t)n) < 0) { /* abaikan */ }
    _exit(128 + sig);
}

static void hook_code(uc_engine *uc, uint64_t addr, uint32_t size, void *ud)
{
    (void)uc; (void)size; (void)ud;
    if (addr == RET_SENTINEL) { g_stop = 2; uc_emu_stop(g_uc); return; }
    uint32_t idx = ((uint32_t)addr - TRAP_BASE) / 16;
    uint32_t lr = RLR();
    for (int i = 0; i < g_nhle; i++) {
        Hle *h = &g_hle[i];
        if (h->is_data || h->addr != (uint32_t)addr) continue;
        h->calls++;
        g_lasthle = h->name;
        uint32_t a[8];
        for (int k = 0; k < 8; k++) a[k] = R(3 + k);
        if (!h->fn && h->calls <= 3)
            LOG("[HLE-GENERIK] %s(%08x,%08x,%08x,%08x) dari %s\n", h->name, a[0], a[1], a[2], a[3], describe(lr));
        else if (h->fn && (g_trace || h->fn == h_nsappmain || h->fn == h_exit || h->fn == h_abort))
            LOG("[HLE] %s dari %s\n", h->name, describe(lr));
        uint32_t ret = h->fn ? h->fn(a) : 0;
        if (g_tail) { uint32_t t = g_tail; g_tail = 0; WPC(t); return; }   /* lompat ke IMP guest, LR tetap */
        W(3, ret);
        if (g_use_r4) { W(4, g_r4); g_use_r4 = 0; }
        WPC(lr);
        if (g_stop) uc_emu_stop(g_uc);
        return;
    }
    LOG("[HLE] slot %u tanpa entri @%08x\n", idx, (uint32_t)addr);
    WPC(lr);
}

static bool hook_unmapped(uc_engine *uc, uc_mem_type type, uint64_t address, int size, int64_t value, void *ud)
{
    (void)uc; (void)value; (void)ud;
    LOG("!! akses memori tak terpetakan: type=%d addr=%08x size=%d\n", (int)type, (uint32_t)address, size);
    return false;
}

static double now_s(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

/* jalankan emulasi mulai dari pc sampai sentinel / stop / error / timeout */
static int run_guest(uint32_t pc, double max_seconds)
{
    g_stop = 0;
    double t0 = now_s();
    while (1) {
        uc_err e = uc_emu_start(g_uc, pc, 0xFFFFFFFFull, 5 * 1000000ull, 0);
        if (g_stop) return g_stop;                      /* 1 = stop permintaan HLE, 2 = sentinel */
        if (e != UC_ERR_OK) {
            char why[200];
            snprintf(why, sizeof why, "emulator error: %s", uc_strerror(e));
            dump_state(why);
            return -1;
        }
        pc = RPC();
        if (now_s() - t0 > max_seconds) {
            dump_state("timeout (kemungkinan loop tak berujung)");
            return -2;
        }
    }
}

static int call_guest(uint32_t fn, double max_seconds)
{
    W(1, INIT_SP);
    WLR(RET_SENTINEL);
    return run_guest(fn, max_seconds);
}



/* ===================== bootstrap M2: meniru NSApplicationMain + timer ===================== */
static int call_guest_args(uint32_t fn, uint32_t a0, uint32_t a1, uint32_t a2, double secs)
{
    W(3, a0); W(4, a1); W(5, a2);
    W(1, INIT_SP);
    WLR(RET_SENTINEL);
    return run_guest(fn, secs);
}

static uint32_t imp_for(uint32_t obj, const char *sel)
{
    Recv r = classify(obj);
    for (GClass *g = r.gc; g; g = find_gclass(g->super)) {
        uint32_t imp = find_imp(g->cls, sel);
        if (imp) return imp;
    }
    return 0;
}

static void stage2(int frames)
{
    LOG("\n===== BOOTSTRAP M2 =====\n");
    GClass *ctl = find_gclass("LuxorController");
    if (!ctl) { LOG("LuxorController tidak ditemukan\n"); return; }
    uint32_t app = the_app(find_gclass("LuxorApplication"));
    uint32_t obj = new_obj_guest(ctl);
    LOG("NSApp=%08x  LuxorController=%08x\n", app, obj);

    uint32_t imp = find_imp(ctl->cls, "applicationDidFinishLaunching:");
    LOG("-> applicationDidFinishLaunching: imp=%08x\n", imp);
    if (!imp) return;
    int r = call_guest_args(imp, obj, intern("applicationDidFinishLaunching:"), 0, 90.0);
    LOG("applicationDidFinishLaunching: selesai, kode=%d (%s)\n", r, g_stop_reason);
    if (r != 2) return;

    uint32_t tgt = g_timer_target ? g_timer_target : obj;
    uint32_t sel = g_timer_sel ? g_timer_sel : intern("gameLoop:");
    uint32_t loop = imp_for(tgt, cs(sel));
    LOG("timer: target=%08x selector=\"%s\" imp=%08x\n", tgt, cs(sel), loop);
    if (!loop) { LOG("tidak ada IMP untuk selector timer\n"); return; }
    for (int f = 0; f < frames; f++) {
        g_curframe = f;
        g_trace = (f < 2);                         /* catat setiap panggilan HLE pada 2 frame pertama */
        if (f < 3) LOG("frame %d mulai\n", f);
        r = call_guest_args(loop, tgt, sel, 0, 20.0);
        if (r != 2) { LOG("frame %d berhenti, kode=%d (%s)\n", f, r, g_stop_reason); break; }
        if (f < 3 || f % 30 == 0) LOG("frame %d selesai\n", f);
    }
    LOG("===== BOOTSTRAP M2 SELESAI =====\n");
}

/* ------------------------------------------------ diagnostik memori host */
static void log_file_head(const char *path, int maxlines)
{
    FILE *f = fopen(path, "r");
    if (!f) { LOG("  %s: tidak bisa dibuka (%s)\n", path, strerror(errno)); return; }
    char line[200];
    for (int i = 0; i < maxlines && fgets(line, sizeof line, f); i++) LOG("  %s: %s", path, line);
    fclose(f);
}

static void probe_rwx(void)
{
    LOG("== Diagnostik memori host ==\n");
    log_file_head("/proc/meminfo", 4);
    log_file_head("/proc/sys/vm/overcommit_memory", 1);
    static const int mbs[] = {512, 256, 128, 64, 32, 16, 8};
    for (size_t i = 0; i < sizeof mbs / sizeof mbs[0]; i++) {
        size_t sz = (size_t)mbs[i] << 20;
        void *p = mmap(NULL, sz, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (p == MAP_FAILED) { LOG("  probe %3d MB: mmap gagal (%s)\n", mbs[i], strerror(errno)); continue; }
        int r = mprotect(p, sz, PROT_READ | PROT_WRITE | PROT_EXEC);
        LOG("  probe %3d MB: %s\n", mbs[i], r == 0 ? "OK (baca+tulis+eksekusi)" : strerror(errno));
        munmap(p, sz);
    }
}

static void setup_cpu(void)
{
    uc_err e = uc_open(UC_ARCH_PPC, (uc_mode)(UC_MODE_PPC32 | UC_MODE_BIG_ENDIAN), &g_uc);
    if (e != UC_ERR_OK) { LOG("FATAL: uc_open PPC32 gagal: %s\n", uc_strerror(e)); exit(2); }
#ifdef LUXOR_CPU_MODEL
    e = uc_ctl_set_cpu_model(g_uc, LUXOR_CPU_MODEL);
    LOG("CPU model: %s -> %s\n", LUXOR_CPU_MODEL_STR, uc_strerror(e));
#else
    LOG("CPU model: default Unicorn (tidak diset)\n");
#endif
#if defined(HAVE_TCG_BUFFER_CTL) || defined(uc_ctl_set_tcg_buffer_size)
    if (g_tcg_mb > 0) {
        e = uc_ctl_set_tcg_buffer_size(g_uc, (uint32_t)g_tcg_mb * 1024u * 1024u);
        LOG("TCG buffer: %d MB -> %s\n", g_tcg_mb, uc_strerror(e));
    }
#else
    LOG("TCG buffer: kontrol tidak tersedia di build ini\n");
#endif
}

static void enable_fpu_altivec(void)
{
    uint32_t msr = 0;
    uc_reg_read(g_uc, UC_PPC_REG_MSR, &msr);
    msr |= (1u << 13) | (1u << 25);                      /* FP | VEC */
    uc_reg_write(g_uc, UC_PPC_REG_MSR, &msr);
}

static void install_hooks(void)
{
    uc_hook h1, h2, h3, h4;
    uc_hook_add(g_uc, &h1, UC_HOOK_CODE, (void *)hook_code, NULL, TRAP_BASE, TRAP_BASE + TRAP_SIZE - 1);
    uc_hook_add(g_uc, &h2, UC_HOOK_MEM_READ_UNMAPPED | UC_HOOK_MEM_WRITE_UNMAPPED | UC_HOOK_MEM_FETCH_UNMAPPED,
                (void *)hook_unmapped, NULL, 1, 0);
    if (g_blocktrace) uc_hook_add(g_uc, &h3, UC_HOOK_BLOCK, (void *)hook_block, NULL, 1, 0);
    if (g_insntrace) uc_hook_add(g_uc, &h4, UC_HOOK_CODE, (void *)hook_insn, NULL, 1, 0);
}
#endif /* !DRYRUN */


static const HleDef *hle_def_find(const char *name)
{
    for (const HleDef *d = g_defs; d->name; d++)
        if (!strcmp(d->name, name)) return d;
    return NULL;
}

/* ----------------------------------------------------------------- main */
static void print_image_report(Image *im)
{
    LOG("  [%2d] %-14s slide=%08x  guest=[%08x..%08x)  dep=%d  extrel=%d(addend!=0:%d) rebase=%d lazy=%d nonlazy=%d nl_local+slide=%d odd=%d\n",
        im->idx, im->short_name, im->slide, im->lo, im->hi, im->ndeps, im->n_extrel, im->n_extrel_addend,
        im->n_rebase, im->n_lazy, im->n_nonlazy, im->n_nl_local, im->n_odd_reloc);
}

int main(int argc, char **argv)
{
    const char *app = argc > 1 ? argv[1] : "Luxor_Mac/Luxor.app";
    for (int i = 2; i < argc; i++) {
#ifndef DRYRUN
        if (!strcmp(argv[i], "--trace")) g_trace = 1;
        else if (!strcmp(argv[i], "--tcg-mb") && i + 1 < argc) g_tcg_mb = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--frames") && i + 1 < argc) g_frames = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--no-boot")) g_noboot = 1;
        else if (!strcmp(argv[i], "--fast")) g_blocktrace = 0;
        else if (!strcmp(argv[i], "--insn")) g_insntrace = 1;
#endif
    }
    g_logf = fopen("loader_log.txt", "w");
    LOG("luxor_mac_loader M1 (probe)\napp: %s\n", app);
#ifndef DRYRUN
    signal(SIGABRT, crash_handler);
    signal(SIGSEGV, crash_handler);
    signal(SIGBUS, crash_handler);
    signal(SIGFPE, crash_handler);
    signal(SIGILL, crash_handler);
#endif

#ifndef DRYRUN
    probe_rwx();
    setup_cpu();
#endif
    char exe[700];
    snprintf(g_exe_dir, sizeof g_exe_dir, "%s/Contents/MacOS", app);
    snprintf(exe, sizeof exe, "%s/Luxor", g_exe_dir);

    /* region umum */
    map_region("heap", HEAP_BASE, HEAP_SIZE);
    map_region("hle-data", DATA_BASE, DATA_SIZE);
    map_region("hle-trap", TRAP_BASE, TRAP_SIZE);
    wbe32(g2h(TRAP_BASE, 4), 0x4e800020);                      /* slot 0 (sentinel) = blr */
    hle_state_init();
    snprintf(g_app_path, sizeof g_app_path, "%s", app);
    {
        char cwd[500];
        if (!getcwd(cwd, sizeof cwd)) snprintf(cwd, sizeof cwd, ".");
        snprintf(g_appdata, sizeof g_appdata, "%s/appdata", cwd);
        mkdir(g_appdata, 0755);
        LOG("appdata: %s\n", g_appdata);
    }
    map_region("stack", STACK_TOP - STACK_SIZE, STACK_SIZE);

    /* muat image: exe lebih dulu (indeks 0), lalu framework */
    Image *mainimg = load_image(exe, 1);
    snprintf(mainimg->install, sizeof mainimg->install, "<exe>");
    load_tree(mainimg);

    LOG("\n== Image termuat: %d, export global: %zu ==\n", g_nimg, g_nexp);

    for (int i = 0; i < g_nimg; i++) fixup_image(g_img[i]);
    objc_register_classes(g_img[0]);
    /* isi section __DATA,__dyld seperti yang dilakukan dyld asli (crt1 memeriksa ini) */
    for (int i = 0; i < g_nimg; i++) {
        Image *im = g_img[i];
        for (int si = 0; si < im->nsects; si++) {
            Sect *t = &im->sects[si];
            if (strcmp(t->seg, "__DATA") || strcmp(t->name, "__dyld") || t->size < 8) continue;
            uint8_t *p = g2h(t->addr + im->slide, 8);
            if (!p) continue;
            wbe32(p, hle_symbol("<dyld_lazy_binder>", 0));
            wbe32(p + 4, hle_symbol("<dyld_func_lookup>", 0));
            LOG("  __dyld %s: diisi\n", im->short_name);
        }
    }
    for (int i = 0; i < g_nimg; i++) print_image_report(g_img[i]);
    print_hle_summary();

    LOG("\n== Urutan inisialisasi ==\n");
    for (int i = 0; i < g_norder; i++) {
        Image *im = g_order[i];
        for (int s = 0; s < im->nsects; s++) {
            Sect *t = &im->sects[s];
            if ((t->flags & 0xff) != 9) continue;
            for (uint32_t k = 0; k < t->size / 4; k++) {
                uint8_t *p = g2h(t->addr + im->slide + k * 4, 4);
                LOG("  %-14s init[%u] = %s\n", im->short_name, k, p ? describe(be32(p)) : "?");
            }
        }
    }
    LOG("\nentry exe = %08x (%s)\n", mainimg->entry, describe(mainimg->entry));

#ifdef DRYRUN
    g_logcut = 0;
    print_unimplemented();
    LOG("\nDRYRUN selesai (emulator tidak dijalankan).\n");
    return 0;
#else
    enable_fpu_altivec();
    install_hooks();

    /* jalankan initializer: dependensi dulu, exe terakhir */
    for (int i = 0; i < g_norder; i++) {
        Image *im = g_order[i];
        for (int s = 0; s < im->nsects; s++) {
            Sect *t = &im->sects[s];
            if ((t->flags & 0xff) != 9) continue;
            for (uint32_t k = 0; k < t->size / 4; k++) {
                uint8_t *p = g2h(t->addr + im->slide + k * 4, 4);
                uint32_t fn = p ? be32(p) : 0;
                if (!fn || fn == 0xffffffffu) continue;
                LOG("-> init %s[%u] @ %s\n", im->short_name, k, describe(fn));
                int r = call_guest(fn, 30.0);
                if (r != 2) { LOG("initializer tidak kembali normal (kode %d): %s\n", r, g_stop_reason); goto done; }
            }
        }
    }

    /* stack awal: [argc][argv0][0][envp: kosong][0][apple0][0] */
    {
        uint32_t sp = STACK_TOP - 0x1000;
        char path[700];
        snprintf(path, sizeof path, "%s", exe);
        uint32_t slen = (uint32_t)strlen(path) + 1;
        uint32_t sa = sp - 0x400;
        memcpy(g2h(sa, slen), path, slen);
        sp -= 0x800;
        uint8_t *st = g2h(sp, 32);
        wbe32(st + 0, 1);            /* argc */
        wbe32(st + 4, sa);           /* argv[0] */
        wbe32(st + 8, 0);            /* argv terminator */
        wbe32(st + 12, 0);           /* envp terminator */
        wbe32(st + 16, sa);          /* apple[0] */
        wbe32(st + 20, 0);
        W(1, sp);
        WLR(RET_SENTINEL);
        LOG("\n-> start (entry %08x), sp=%08x\n", mainimg->entry, sp);
        int r = run_guest(mainimg->entry, 120.0);
        LOG("\nhasil run_guest = %d: %s\n", r, g_stop_reason);
        if (r == 1 && g_boot && !g_noboot) stage2(g_frames);
    }
done:
    g_logcut = 0;
    print_call_stats();
    print_unimplemented();
    LOG("\nSelesai.\n");
    return 0;
#endif
}
