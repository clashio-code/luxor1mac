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
#include <sys/mman.h>
#include <sys/stat.h>

#ifndef DRYRUN
#include <unicorn/unicorn.h>
static uc_engine *g_uc;
#endif

/* ------------------------------------------------------------------ log */
static FILE *g_logf;
static void LOG(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
    if (g_logf) {
        va_start(ap, fmt);
        vfprintf(g_logf, fmt, ap);
        va_end(ap);
        fflush(g_logf);
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

static uint32_t hle_symbol(const char *name, int want_data)
{
    Hle *h = hle_find(name);
    if (h) {
        if (want_data == 1 && !h->is_data)
            LOG("WARN: simbol %s dipakai sebagai data tapi sudah jadi fungsi\n", name);
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
        uint32_t sz = 256;
        if (!strcmp(name, "___sF")) sz = 0x400;
        else if (strstr(name, "RuneLocale")) sz = 0x3000;
        h->addr = data_alloc(sz);
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
#ifndef DRYRUN

static int g_stop;
static const char *g_stop_reason = "";
static int g_trace = 0;

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
    backtrace();
}

/* ---- handler HLE ---- */
#define H(n) static uint32_t n(uint32_t *a)
#define UNUSED (void)a

H(h_malloc)  { return heap_alloc(a[0]); }
H(h_calloc)  { uint32_t n = a[0] * a[1]; return heap_alloc(n); }       /* mmap sudah nol */
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
H(h_strlen)  { const uint8_t *s = g2h(a[0], 1); return s ? (uint32_t)strlen((const char *)s) : 0; }
H(h_strcmp)  { const uint8_t *x = g2h(a[0], 1), *y = g2h(a[1], 1); return (x && y) ? (uint32_t)strcmp((const char *)x, (const char *)y) : 0; }
H(h_strncmp) { const uint8_t *x = g2h(a[0], 1), *y = g2h(a[1], 1); return (x && y) ? (uint32_t)strncmp((const char *)x, (const char *)y, a[2]) : 0; }
H(h_strcpy)  { uint8_t *d = g2h(a[0], 1); const uint8_t *s = g2h(a[1], 1); if (d && s) { size_t n = strlen((const char *)s) + 1; uint8_t *d2 = g2h(a[0], n); if (d2) memmove(d2, s, n); } return a[0]; }
H(h_strncpy) { uint8_t *d = g2h(a[0], a[2]); const uint8_t *s = g2h(a[1], 1); if (d && s) strncpy((char *)d, (const char *)s, a[2]); return a[0]; }
H(h_strchr)  { const uint8_t *s = g2h(a[0], 1); if (!s) return 0; const char *r = strchr((const char *)s, (int)a[1]); return r ? a[0] + (uint32_t)(r - (const char *)s) : 0; }
H(h_strrchr) { const uint8_t *s = g2h(a[0], 1); if (!s) return 0; const char *r = strrchr((const char *)s, (int)a[1]); return r ? a[0] + (uint32_t)(r - (const char *)s) : 0; }
H(h_zero)    { UNUSED; return 0; }
H(h_one)     { UNUSED; return 1; }
H(h_getenv)  { UNUSED; return 0; }
H(h_abort)   { UNUSED; g_stop = 1; g_stop_reason = "abort() dipanggil oleh game"; return 0; }
H(h_exit)    { g_stop = 1; g_stop_reason = "exit() dipanggil oleh game"; LOG("  exit(%d)\n", (int)a[0]); return 0; }
H(h_new)     { return heap_alloc(a[0]); }
H(h_log_fmt) { LOG("    fmt=\"%s\"\n", gstr(a[0])); return 0; }
H(h_log_fmt2){ LOG("    fmt=\"%s\"\n", gstr(a[1])); return 0; }
H(h_puts)    { LOG("    puts: %s\n", gstr(a[0])); return 1; }
H(h_msgsend) {
    LOG("    objc_msgSend(self=%08x, sel=\"%s\")\n", a[0], gstr(a[1]));
    return 0;
}
H(h_nsappmain) {
    UNUSED;
    g_stop = 1;
    g_stop_reason = "MILESTONE 1 TERCAPAI: NSApplicationMain() dipanggil";
    return 0;
}
static uint32_t g_tls_key = 1;
H(h_key_create) { uint8_t *p = g2h(a[0], 4); if (p) wbe32(p, g_tls_key++); return 0; }
static uint32_t g_tls[64];
H(h_getspecific) { return a[0] < 64 ? g_tls[a[0]] : 0; }
H(h_setspecific) { if (a[0] < 64) g_tls[a[0]] = a[1]; return 0; }

static const HleDef g_defs[] = {
    {"_malloc", h_malloc}, {"_calloc", h_calloc}, {"_free", h_free}, {"_realloc", h_realloc},
    {"_valloc", h_malloc}, {"_memalign", h_malloc},
    {"_memcpy", h_memcpy}, {"_memmove", h_memcpy}, {"_memset", h_memset}, {"_memcmp", h_memcmp},
    {"_bcopy", h_zero},
    {"_strlen", h_strlen}, {"_strcmp", h_strcmp}, {"_strncmp", h_strncmp},
    {"_strcpy", h_strcpy}, {"_strncpy", h_strncpy}, {"_strchr", h_strchr}, {"_strrchr", h_strrchr},
    {"_abort", h_abort}, {"_exit", h_exit}, {"__exit", h_exit},
    {"__Znwm", h_new}, {"__Znam", h_new}, {"__ZdlPv", h_free}, {"__ZdaPv", h_free},
    {"_getenv", h_getenv}, {"_atexit", h_zero}, {"___cxa_atexit", h_zero},
    {"__mach_init_routine", h_zero}, {"__cthread_init_routine", h_zero},
    {"__dyld_register_func_for_add_image", h_zero}, {"__dyld_register_func_for_remove_image", h_zero},
    {"_getpid", h_one},
    {"_pthread_self", h_one}, {"_pthread_mutex_init", h_zero}, {"_pthread_mutex_lock", h_zero},
    {"_pthread_mutex_unlock", h_zero}, {"_pthread_mutex_destroy", h_zero},
    {"_pthread_mutexattr_init", h_zero}, {"_pthread_mutexattr_settype", h_zero},
    {"_pthread_mutexattr_destroy", h_zero}, {"_pthread_cond_init", h_zero},
    {"_pthread_key_create", h_key_create}, {"_pthread_getspecific", h_getspecific},
    {"_pthread_setspecific", h_setspecific},
    {"_printf", h_log_fmt}, {"_fprintf", h_log_fmt2}, {"_sprintf", h_log_fmt2}, {"_snprintf", h_log_fmt},
    {"_puts", h_puts}, {"_NSLog", h_log_fmt},
    {"_objc_msgSend", h_msgsend},
    {"_NSApplicationMain", h_nsappmain},
    {NULL, NULL}
};

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
        uint32_t a[8];
        for (int k = 0; k < 8; k++) a[k] = R(3 + k);
        if (!h->fn && h->calls <= 3)
            LOG("[HLE-GENERIK] %s(%08x,%08x,%08x,%08x) dari %s\n", h->name, a[0], a[1], a[2], a[3], describe(lr));
        else if (h->fn && (g_trace || h->fn == h_msgsend || h->fn == h_nsappmain || h->fn == h_exit || h->fn == h_abort))
            LOG("[HLE] %s dari %s\n", h->name, describe(lr));
        uint32_t ret = h->fn ? h->fn(a) : 0;
        W(3, ret);
        WPC(lr);
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
    uc_hook h1, h2;
    uc_hook_add(g_uc, &h1, UC_HOOK_CODE, (void *)hook_code, NULL, TRAP_BASE, TRAP_BASE + TRAP_SIZE - 1);
    uc_hook_add(g_uc, &h2, UC_HOOK_MEM_READ_UNMAPPED | UC_HOOK_MEM_WRITE_UNMAPPED | UC_HOOK_MEM_FETCH_UNMAPPED,
                (void *)hook_unmapped, NULL, 1, 0);
}
#endif /* !DRYRUN */

/* ------------------------------------------------ definisi tabel (dry run) */
#ifdef DRYRUN
static const HleDef g_defs[] = {
    {"_malloc", NULL}, {"_calloc", NULL}, {"_free", NULL}, {"_realloc", NULL}, {"_memcpy", NULL}, {"_memmove", NULL},
    {"_memset", NULL}, {"_memcmp", NULL}, {"_strlen", NULL}, {"_strcmp", NULL}, {"_strncmp", NULL}, {"_strcpy", NULL},
    {"_strncpy", NULL}, {"_strchr", NULL}, {"_strrchr", NULL}, {"_abort", NULL}, {"_exit", NULL}, {"__exit", NULL},
    {"__Znwm", NULL}, {"__Znam", NULL}, {"__ZdlPv", NULL}, {"__ZdaPv", NULL}, {"_getenv", NULL}, {"_atexit", NULL},
    {"___cxa_atexit", NULL}, {"__mach_init_routine", NULL}, {"__cthread_init_routine", NULL},
    {"__dyld_register_func_for_add_image", NULL}, {"__dyld_register_func_for_remove_image", NULL},
    {"_getpid", NULL}, {"_pthread_self", NULL}, {"_pthread_mutex_init", NULL}, {"_pthread_mutex_lock", NULL},
    {"_pthread_mutex_unlock", NULL}, {"_pthread_mutex_destroy", NULL}, {"_pthread_key_create", NULL},
    {"_pthread_getspecific", NULL}, {"_pthread_setspecific", NULL}, {"_printf", NULL}, {"_NSLog", NULL},
    {"_objc_msgSend", NULL}, {"_NSApplicationMain", NULL}, {NULL, NULL}
};
#endif

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
#endif
    }
    g_logf = fopen("loader_log.txt", "w");
    LOG("luxor_mac_loader M1 (probe)\napp: %s\n", app);

#ifndef DRYRUN
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
    map_region("stack", STACK_TOP - STACK_SIZE, STACK_SIZE);

    /* muat image: exe lebih dulu (indeks 0), lalu framework */
    Image *mainimg = load_image(exe, 1);
    snprintf(mainimg->install, sizeof mainimg->install, "<exe>");
    load_tree(mainimg);

    LOG("\n== Image termuat: %d, export global: %zu ==\n", g_nimg, g_nexp);

    for (int i = 0; i < g_nimg; i++) fixup_image(g_img[i]);
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
    }
done:
    print_unimplemented();
    LOG("\nSelesai.\n");
    return 0;
#endif
}
