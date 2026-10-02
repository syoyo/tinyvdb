/* Audit regressions: each case reproduces a defect found in review.
 *
 * Inputs are crafted in memory (byte builders, or mutated copies of writer
 * output); argv[1] is the generated sphere.vdb fixture. A counting allocator
 * checks leaks, free/realloc size agreement and caps total live bytes so
 * header-driven allocations show up as failures instead of huge requests. */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L /* mkstemp, write, unlink */
#endif
#include "tinyvdb_io.h"
#include "tinyvdb_nanovdb.h"
#include "lz4.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#if !defined(_WIN32)
#include <unistd.h>
#endif

/* Make sanitizer diagnostics fatal so UB on a crafted input fails the test
   (the signed-overflow findings are only observable this way). */
const char *__ubsan_default_options(void);
const char *__ubsan_default_options(void) { return "halt_on_error=1:print_stacktrace=1"; }

static int failures;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #c); ++failures; } } while (0)

static const char *g_fixture;

/* ------------------------------------------------------------------------ */
/*  Counting allocator                                                       */
/* ------------------------------------------------------------------------ */

typedef struct ctr {
    size_t live_bytes, peak_bytes, cap_bytes;
    long   live_count, mismatches, frees, calls;
    long   fail_at;     /* fail the Nth malloc/realloc call (0-based), -1 off */
    size_t fail_size;   /* fail any malloc of exactly this size, 0 off */
    size_t realloc_limit; /* fail reallocs growing past this, 0 off */
} ctr_t;

typedef struct { size_t size; size_t pad; } ctr_hdr_t;

static void ctr_init(ctr_t *c) {
    memset(c, 0, sizeof(*c));
    c->cap_bytes = (size_t)256 << 20;
    c->fail_at = -1;
}

/* Counts one allocator call; nonzero when this call must fail. */
static int ctr_refuse(ctr_t *c, size_t growth) {
    long call = c->calls++;
    if (c->fail_at >= 0 && call == c->fail_at) return 1;
    return growth > c->cap_bytes || c->live_bytes > c->cap_bytes - growth;
}

static void *ctr_raw(ctr_t *c, size_t n) {
    ctr_hdr_t *h = (ctr_hdr_t *)malloc(sizeof(ctr_hdr_t) + (n ? n : 1));
    if (!h) return NULL;
    h->size = n;
    memset(h + 1, 0xA5, n);
    c->live_bytes += n;
    c->live_count++;
    if (c->live_bytes > c->peak_bytes) c->peak_bytes = c->live_bytes;
    return h + 1;
}

static void ctr_release(ctr_t *c, void *p) {
    ctr_hdr_t *h = (ctr_hdr_t *)p - 1;
    c->live_bytes -= h->size;
    c->live_count--;
    free(h);
}

static void *ctr_malloc(size_t n, void *ctx) {
    ctr_t *c = (ctr_t *)ctx;
    if (ctr_refuse(c, n) || (c->fail_size && n == c->fail_size)) return NULL;
    return ctr_raw(c, n);
}

static void ctr_free(void *p, size_t n, void *ctx) {
    ctr_t *c = (ctr_t *)ctx;
    if (!p) return;
    if (((ctr_hdr_t *)p - 1)->size != n) c->mismatches++;
    c->frees++;
    ctr_release(c, p);
}

static void *ctr_realloc(void *p, size_t o, size_t n, void *ctx) {
    ctr_t *c = (ctr_t *)ctx;
    if (!p) return ctr_malloc(n, ctx);
    size_t have = ((ctr_hdr_t *)p - 1)->size;
    if (have != o) c->mismatches++;
    if (ctr_refuse(c, n > have ? n - have : 0)) return NULL;
    if (c->realloc_limit && n > c->realloc_limit) return NULL;
    void *q = ctr_raw(c, n);
    if (!q) return NULL;
    memcpy(q, p, have < n ? have : n);
    ctr_release(c, p);
    return q;
}

static tvdb_allocator_t ctr_alloc(ctr_t *c) {
    tvdb_allocator_t a = { ctr_malloc, ctr_realloc, ctr_free, c };
    return a;
}

/* ------------------------------------------------------------------------ */
/*  Byte builder                                                             */
/* ------------------------------------------------------------------------ */

typedef struct { uint8_t *d; size_t n, cap; } bb_t;

static void bb_put(bb_t *b, const void *src, size_t n) {
    if (b->n + n > b->cap) {
        size_t nc = b->cap ? b->cap : 1024;
        while (nc < b->n + n) nc *= 2;
        uint8_t *d = (uint8_t *)realloc(b->d, nc);
        if (!d) { fprintf(stderr, "test OOM\n"); exit(2); }
        b->d = d; b->cap = nc;
    }
    if (n) memcpy(b->d + b->n, src, n);
    b->n += n;
}
static void bb_u8(bb_t *b, uint8_t v) { bb_put(b, &v, 1); }
static void bb_u32(bb_t *b, uint32_t v) { bb_put(b, &v, 4); }
static void bb_i32(bb_t *b, int32_t v) { bb_put(b, &v, 4); }
static void bb_i64(bb_t *b, int64_t v) { bb_put(b, &v, 8); }
static void bb_u64(bb_t *b, uint64_t v) { bb_put(b, &v, 8); }
static void bb_f32(bb_t *b, float v) { bb_put(b, &v, 4); }
static void bb_f64(bb_t *b, double v) { bb_put(b, &v, 8); }
static void bb_fill(bb_t *b, uint8_t v, size_t n) {
    for (size_t i = 0; i < n; ++i) bb_u8(b, v);
}
static void bb_str(bb_t *b, const char *s, size_t n) {
    bb_u32(b, (uint32_t)n);
    bb_put(b, s, n);
}
static void bb_cstr(bb_t *b, const char *s) { bb_str(b, s, strlen(s)); }
static void bb_free(bb_t *b) { free(b->d); memset(b, 0, sizeof(*b)); }

/* Node mask with only slot 0 set (`bytes` long). */
static void bb_mask_slot0(bb_t *b, size_t bytes) {
    bb_u8(b, 1);
    bb_fill(b, 0, bytes - 1);
}

static void put_header(bb_t *b, uint32_t version) {
    bb_i64(b, 0x56444220);
    bb_u32(b, version);
    bb_u32(b, 10);
    bb_u32(b, 0);
    bb_u8(b, 1); /* has grid offsets */
    if (version >= 220 && version < 222) bb_u8(b, 0); /* not compressed */
    bb_fill(b, '0', 36);
}

static void put_grid_prefix(bb_t *b, uint32_t version, uint32_t comp) {
    if (version >= 222) bb_u32(b, comp);
    bb_i32(b, 0); /* grid metadata count */
    bb_cstr(b, "UniformScaleMap");
    for (int i = 0; i < 15; ++i) bb_f64(b, 1.0);
    bb_i32(b, 1); /* tree buffer count */
}

/* Complete one-grid file around `payload`. */
static bb_t make_file(uint32_t version, const char *name, size_t name_len,
                      const char *gtype, const bb_t *payload) {
    bb_t f = { 0 };
    put_header(&f, version);
    bb_i32(&f, 0); /* file metadata count */
    bb_i32(&f, 1); /* grid count */
    bb_str(&f, name, name_len);
    bb_cstr(&f, gtype);
    if (version >= 221) bb_cstr(&f, "");
    uint64_t off = f.n + 24;
    bb_u64(&f, off);
    bb_u64(&f, off);
    bb_u64(&f, off + payload->n);
    bb_put(&f, payload->d, payload->n);
    return f;
}

/* Root with one child -> upper slot 0 -> lower slot 0 -> one leaf, v224,
 * per-node flag 6 with uncompressed values. `elem` is the stored element
 * size; internal values are zero (also zero as half). */
static void put_chain(bb_t *b, const void *bg, size_t bg_size, size_t elem,
                      const uint8_t leaf_mask[64], const void *leaf_vals) {
    bb_put(b, bg, bg_size);
    bb_u32(b, 0);
    bb_u32(b, 1);
    bb_i32(b, 0); bb_i32(b, 0); bb_i32(b, 0);
    bb_mask_slot0(b, 4096); bb_fill(b, 0, 4096);
    bb_u8(b, 6); bb_fill(b, 0, 32768 * elem);
    bb_mask_slot0(b, 512); bb_fill(b, 0, 512);
    bb_u8(b, 6); bb_fill(b, 0, 4096 * elem);
    bb_put(b, leaf_mask, 64);
    bb_put(b, leaf_mask, 64);
    bb_u8(b, 6);
    bb_put(b, leaf_vals, 512 * elem);
}

static uint16_t f2h(float f) { /* exact for the small values used here */
    uint32_t u; memcpy(&u, &f, 4);
    if ((u & 0x7fffffffu) == 0) return (uint16_t)(u >> 16);
    uint32_t sign = u >> 31, exp = (u >> 23) & 0xff, mant = u & 0x7fffff;
    return (uint16_t)((sign << 15) | ((exp - 127 + 15) << 10) | (mant >> 13));
}

static tvdb_status_t open_read(tvdb_file_t *f, const bb_t *b,
                               const tvdb_allocator_t *a, tvdb_error_t *e) {
    tvdb_status_t st = tvdb_file_open_memory(f, b->d, b->n, a, e);
    if (st != TVDB_OK) return st;
    return tvdb_read_all_grids(f, e);
}

static int contains(const uint8_t *d, size_t n, const char *needle) {
    size_t k = strlen(needle);
    for (size_t i = 0; i + k <= n; ++i)
        if (!memcmp(d + i, needle, k)) return 1;
    return 0;
}

/* Value of the first "is_saved_as_half_float" bool entry, or -1. */
static int meta_half_flag(const uint8_t *d, size_t n) {
    static const char key[] = "is_saved_as_half_float";
    size_t k = sizeof(key) - 1;
    for (size_t i = 0; i + k + 4 + 4 + 4 + 1 <= n; ++i) {
        if (memcmp(d + i, key, k)) continue;
        const uint8_t *t = d + i + k;
        uint32_t tl, vl;
        memcpy(&tl, t, 4);
        if (tl != 4 || memcmp(t + 4, "bool", 4)) continue;
        memcpy(&vl, t + 8, 4);
        if (vl != 1) continue;
        return t[12];
    }
    return -1;
}

static float float_at(const uint8_t *p, size_t idx) {
    float v; memcpy(&v, p + idx * 4, 4); return v;
}

/* NanoVDB FloatGrid of the fixture, with taper forced to 1 so the buffer is
 * accepted even by readers that predate the converter fix. */
static uint8_t *fixture_nano(size_t *n) {
    tvdb_file_t f;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    uint8_t *out = NULL;
    *n = 0;
    if (tvdb_file_open(&f, g_fixture, NULL, &e) != TVDB_OK) return NULL;
    if (tvdb_read_all_grids(&f, &e) == TVDB_OK)
        tvdb_grid_to_nanovdb_float(&f.grids[0], &out, n, &e);
    tvdb_file_close(&f);
    if (out) { double one = 1.0; memcpy(out + 552, &one, 8); }
    return out;
}

/* ------------------------------------------------------------------------ */
/*  Finding 1: v220/221 internal values must be indexed by slot              */
/* ------------------------------------------------------------------------ */

static void test_v221_internal_values_by_slot(void) {
    bb_t p = { 0 };
    put_grid_prefix(&p, 221, 0);
    bb_f32(&p, 3.0f);                     /* background */
    bb_u32(&p, 0); bb_u32(&p, 1);
    bb_i32(&p, 0); bb_i32(&p, 0); bb_i32(&p, 0);
    bb_mask_slot0(&p, 4096); bb_fill(&p, 0, 4096);
    for (int i = 0; i < 32767; ++i) bb_f32(&p, 5.0f); /* non-child slots only */
    bb_mask_slot0(&p, 512); bb_fill(&p, 0, 512);
    for (int i = 0; i < 4095; ++i) bb_f32(&p, 6.0f);
    bb_fill(&p, 0xff, 64);                 /* leaf topology mask */
    bb_fill(&p, 0xff, 64);                 /* leaf buffer: mask */
    bb_i32(&p, 0); bb_i32(&p, 0); bb_i32(&p, 0); bb_u8(&p, 1);
    for (int i = 0; i < 512; ++i) bb_f32(&p, 1.0f);
    bb_t file = make_file(221, "g", 1, "Tree_float_5_4_3", &p);

    tvdb_file_t f;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    CHECK(open_read(&f, &file, NULL, &e) == TVDB_OK);
    if (f.num_grids == 1 && f.grids[0].tree.num_nodes == 4) {
        const tvdb_internal_node_t *up = &f.grids[0].tree.nodes[1].u.internal;
        const tvdb_internal_node_t *lo = &f.grids[0].tree.nodes[2].u.internal;
        CHECK(up->values_size == 32768 * 4);
        CHECK(lo->values_size == 4096 * 4);
        if (up->values_size == 32768 * 4 && lo->values_size == 4096 * 4) {
            CHECK(float_at(up->values, 0) == 3.0f);
            CHECK(float_at(up->values, 1) == 5.0f);
            CHECK(float_at(up->values, 32767) == 5.0f);
            CHECK(float_at(lo->values, 4095) == 6.0f);

            /* Slot-indexed consumers stay in bounds. */
            uint8_t *out = NULL; size_t n = 0;
            CHECK(tvdb_write_to_memory(&f, 0, 0, &out, &n, &e) == TVDB_OK);
            tvdb_file_t g;
            bb_t again = { out, n, n };
            CHECK(open_read(&g, &again, NULL, &e) == TVDB_OK);
            if (g.num_grids == 1 && g.grids[0].tree.num_nodes == 4)
                CHECK(float_at(g.grids[0].tree.nodes[1].u.internal.values,
                               32767) == 5.0f);
            tvdb_file_close(&g);
            free(out);
            uint8_t *nv = NULL;
            CHECK(tvdb_grid_to_nanovdb_float(&f.grids[0], &nv, &n, &e) == TVDB_OK);
            free(nv);
        }
    } else {
        CHECK(!"v221 grid did not load");
    }
    tvdb_file_close(&f);
    bb_free(&file); bb_free(&p);
}

/* ------------------------------------------------------------------------ */
/*  Finding 2: NanoVDB non-float grids must have validated child pointers    */
/* ------------------------------------------------------------------------ */

static void test_nanovdb_nonfloat_child_validation(void) {
    size_t n = 0;
    uint8_t *g = fixture_nano(&n);
    CHECK(g != NULL);
    if (!g) return;
    uint32_t t = TVDB_NANOVDB_GRID_TYPE_INT32;
    memcpy(g + 636, &t, 4);
    uint64_t root; memcpy(&root, g + 672 + 24, 8); root += 672;
    uint64_t tile0 = root + tvdb_nanovdb_root_node_size(t);
    uint64_t delta = (uint64_t)1 << 32; /* 4 GiB past the grid */
    memcpy(g + tile0 + 8, &delta, 8);
    tvdb_nanovdb_file_t nf;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    tvdb_status_t st = tvdb_nanovdb_file_open_memory(&nf, g, n, NULL, &e);
    CHECK(st == TVDB_ERROR_INVALID_DATA);
    if (st == TVDB_OK) tvdb_nanovdb_file_close(&nf); /* do not walk it */
    free(g);
}

/* ------------------------------------------------------------------------ */
/*  Finding 3: root tile/child counts bounded by the remaining bytes         */
/* ------------------------------------------------------------------------ */

static void test_root_counts_bounded(void) {
    for (int which = 0; which < 2; ++which) {
        bb_t p = { 0 };
        put_grid_prefix(&p, 224, 0);
        bb_f32(&p, 3.0f);
        bb_u32(&p, which ? 0 : 0xFFFFFFFFu);
        bb_u32(&p, which ? 0xFFFFFFFFu : 0);
        bb_t file = make_file(224, "g", 1, "Tree_float_5_4_3", &p);
        ctr_t c; ctr_init(&c); c.cap_bytes = (size_t)64 << 20;
        tvdb_allocator_t a = ctr_alloc(&c);
        tvdb_file_t f;
        tvdb_error_t e; memset(&e, 0, sizeof(e));
        clock_t t0 = clock();
        CHECK(open_read(&f, &file, &a, &e) == TVDB_ERROR_INVALID_DATA);
        CHECK((double)(clock() - t0) / CLOCKS_PER_SEC < 2.0);
        CHECK(c.peak_bytes < ((size_t)1 << 20));
        tvdb_file_close(&f);
        CHECK(c.live_count == 0 && c.mismatches == 0);
        bb_free(&file); bb_free(&p);
    }
}

/* ------------------------------------------------------------------------ */
/*  Finding 4: truncated / short payloads must not load as zeros             */
/* ------------------------------------------------------------------------ */

/* zlib stream holding `n` bytes in one stored (uncompressed) deflate block. */
static void put_zlib_stored(bb_t *b, const uint8_t *data, uint16_t n) {
    uint32_t a = 1, s2 = 0;
    for (uint16_t i = 0; i < n; ++i) { a = (a + data[i]) % 65521; s2 = (s2 + a) % 65521; }
    uint32_t adler = (s2 << 16) | a;
    bb_u8(b, 0x78); bb_u8(b, 0x01);
    bb_u8(b, 0x01);
    bb_u8(b, (uint8_t)n); bb_u8(b, (uint8_t)(n >> 8));
    bb_u8(b, (uint8_t)~n); bb_u8(b, (uint8_t)(~n >> 8));
    bb_put(b, data, n);
    bb_u8(b, (uint8_t)(adler >> 24)); bb_u8(b, (uint8_t)(adler >> 16));
    bb_u8(b, (uint8_t)(adler >> 8)); bb_u8(b, (uint8_t)adler);
}

/* Upper and lower nodes stored uncompressed (size prefix -N), then a full
 * leaf mask; the caller appends the leaf value chunk. */
static void put_compressed_chain_head(bb_t *p, uint32_t comp) {
    put_grid_prefix(p, 224, comp);
    bb_f32(p, 3.0f);
    bb_u32(p, 0); bb_u32(p, 1);
    bb_i32(p, 0); bb_i32(p, 0); bb_i32(p, 0);
    bb_mask_slot0(p, 4096); bb_fill(p, 0, 4096);
    bb_u8(p, 6); bb_i64(p, -(int64_t)(32768 * 4)); bb_fill(p, 0, 32768 * 4);
    bb_mask_slot0(p, 512); bb_fill(p, 0, 512);
    bb_u8(p, 6); bb_i64(p, -(int64_t)(4096 * 4)); bb_fill(p, 0, 4096 * 4);
    bb_fill(p, 0xff, 64);
    bb_fill(p, 0xff, 64); /* leaf buffer mask */
    bb_u8(p, 6);
}

static void test_truncated_payloads_rejected(void) {
    uint8_t ones[16];
    for (int i = 0; i < 4; ++i) { float v = 1.0f; memcpy(ones + 4 * i, &v, 4); }
    for (int kind = 0; kind < 4; ++kind) {
        bb_t p = { 0 };
        if (kind == 0) {          /* uncompressed leaf cut short */
            put_grid_prefix(&p, 224, 0);
            bb_f32(&p, 3.0f);
            bb_u32(&p, 0); bb_u32(&p, 1);
            bb_i32(&p, 0); bb_i32(&p, 0); bb_i32(&p, 0);
            bb_mask_slot0(&p, 4096); bb_fill(&p, 0, 4096);
            bb_u8(&p, 6); bb_fill(&p, 0, 32768 * 4);
            bb_mask_slot0(&p, 512); bb_fill(&p, 0, 512);
            bb_u8(&p, 6); bb_fill(&p, 0, 4096 * 4);
            bb_fill(&p, 0xff, 64);
            bb_fill(&p, 0xff, 64); bb_u8(&p, 6); bb_fill(&p, 0x11, 16);
        } else if (kind == 1) {   /* ZIP stream inflates to 16 of 2048 bytes */
            put_compressed_chain_head(&p, TVDB_COMPRESS_ZIP);
            bb_t z = { 0 };
            put_zlib_stored(&z, ones, 16);
            bb_i64(&p, (int64_t)z.n); bb_put(&p, z.d, z.n);
            bb_free(&z);
        } else if (kind == 2) {   /* BLOSC memcpy frame with nbytes = 16 */
            put_compressed_chain_head(&p, TVDB_COMPRESS_BLOSC);
            bb_t fr = { 0 };
            bb_u8(&fr, 2); bb_u8(&fr, 1); bb_u8(&fr, 0x02); bb_u8(&fr, 4);
            bb_i32(&fr, 16); bb_i32(&fr, 16); bb_i32(&fr, 32);
            bb_put(&fr, ones, 16);
            bb_i64(&p, (int64_t)fr.n); bb_put(&p, fr.d, fr.n);
            bb_free(&fr);
        } else {                  /* "-N uncompressed" chunk with wrong N */
            put_compressed_chain_head(&p, TVDB_COMPRESS_ZIP);
            bb_i64(&p, -16); bb_put(&p, ones, 16);
            bb_fill(&p, 0, 4096);
        }
        bb_t file = make_file(224, "g", 1, "Tree_float_5_4_3", &p);
        ctr_t c; ctr_init(&c);
        tvdb_allocator_t a = ctr_alloc(&c);
        tvdb_file_t f;
        tvdb_error_t e; memset(&e, 0, sizeof(e));
        tvdb_status_t st = open_read(&f, &file, &a, &e);
        if (st == TVDB_OK) fprintf(stderr, "truncated payload kind %d loaded\n", kind);
        CHECK(st == TVDB_ERROR_INVALID_DATA ||
              st == TVDB_ERROR_DECOMPRESSION_FAILED);
        tvdb_file_close(&f);
        CHECK(c.live_count == 0 && c.mismatches == 0);
        bb_free(&file); bb_free(&p);
    }
}

/* ------------------------------------------------------------------------ */
/*  Finding 5: inactive values {-bg, X} must round-trip through the writer   */
/* ------------------------------------------------------------------------ */

static void test_mask_two_inactive_values_roundtrip(void) {
    tvdb_file_t f;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    if (tvdb_file_open(&f, g_fixture, NULL, &e) != TVDB_OK ||
        tvdb_read_all_grids(&f, &e) != TVDB_OK) {
        CHECK(!"fixture did not load");
        tvdb_file_close(&f);
        return;
    }
    tvdb_grid_t *g = &f.grids[0];
    float bg = g->tree.nodes[0].u.root.background.u.f;
    size_t leaf_idx = 0;
    for (size_t i = 0; i < g->tree.num_nodes && !leaf_idx; i++) {
        if (g->tree.nodes[i].type != TVDB_NODE_LEAF) continue;
        size_t on = tvdb_nodemask_count_on(&g->tree.nodes[i].u.leaf.value_mask);
        if (on > 0 && on < 500) leaf_idx = i;
    }
    CHECK(leaf_idx != 0);
    if (!leaf_idx) { tvdb_file_close(&f); return; }
    tvdb_leaf_node_t *leaf = &g->tree.nodes[leaf_idx].u.leaf;
    float *v = (float *)leaf->data;
    int k = 0;
    for (int i = 0; i < 512; i++)
        if (!tvdb_nodemask_is_on(&leaf->value_mask, i))
            v[i] = (k++ & 1) ? 7.0f : -bg;
    const uint32_t modes[2] = { TVDB_COMPRESS_ACTIVE_MASK,
                                TVDB_COMPRESS_ACTIVE_MASK | TVDB_COMPRESS_ZIP };
    for (int m = 0; m < 2; ++m) {
        uint8_t *out = NULL; size_t n = 0;
        CHECK(tvdb_write_to_memory(&f, modes[m], 0, &out, &n, &e) == TVDB_OK);
        tvdb_file_t f2;
        bb_t b = { out, n, n };
        CHECK(open_read(&f2, &b, NULL, &e) == TVDB_OK);
        int bad = 0;
        if (f2.num_grids == 1 && f2.grids[0].tree.num_nodes > leaf_idx) {
            const float *w = (const float *)f2.grids[0].tree.nodes[leaf_idx].u.leaf.data;
            for (int i = 0; i < 512; i++) bad += memcmp(&w[i], &v[i], 4) != 0;
        } else {
            bad = 1;
        }
        CHECK(bad == 0);
        tvdb_file_close(&f2);
        free(out);
    }
    tvdb_file_close(&f);
}

/* ------------------------------------------------------------------------ */
/*  Finding 6: NanoVDB writer must not emit raw grids under a codec header   */
/* ------------------------------------------------------------------------ */

static void test_nanovdb_incompressible_grid_codec(void) {
    size_t n = 0;
    uint8_t *g = fixture_nano(&n);
    CHECK(g != NULL);
    if (!g) return;
    /* Minimal empty FloatGrid followed by random padding zlib cannot shrink. */
    size_t base = 672 + 64 + (size_t)tvdb_nanovdb_root_node_size(1);
    /* Large enough that deflate/LZ4 expansion of the random tail outweighs
       what the zero-filled header saves. */
    size_t n2 = base + ((size_t)16 << 20);
    uint8_t *g2 = (uint8_t *)calloc(1, n2);
    memcpy(g2, g, 672);
    uint64_t s64 = n2; memcpy(g2 + 32, &s64, 8);
    uint64_t offs[4] = { 0, 0, 0, 64 }; memcpy(g2 + 672, offs, 32);
    memset(g2 + 704, 0, 32);
    uint32_t x = 12345;
    for (size_t i = base; i < n2; i++) { x = x * 1103515245u + 12345u; g2[i] = (uint8_t)(x >> 16); }
    tvdb_nanovdb_file_t in;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    CHECK(tvdb_nanovdb_file_open_memory(&in, g2, n2, NULL, &e) == TVDB_OK);
    const uint32_t codecs[2] = { TVDB_NANOVDB_CODEC_ZIP, TVDB_NANOVDB_CODEC_BLOSC };
    for (int c = 0; c < 2 && in.num_grids == 1; ++c) {
        uint8_t *out = NULL; size_t outn = 0;
        CHECK(tvdb_nanovdb_write_to_memory(&in, codecs[c], &out, &outn, &e) == TVDB_OK);
        tvdb_nanovdb_file_t back;
        tvdb_status_t st = tvdb_nanovdb_file_open_memory(&back, out, outn, NULL, &e);
        CHECK(st == TVDB_OK);
        if (st == TVDB_OK) {
            CHECK(back.num_grids == 1 && back.grids[0].size == n2 &&
                  memcmp(back.grids[0].data, g2, n2) == 0);
            tvdb_nanovdb_file_close(&back);
        }
        free(out);
    }
    if (in.num_grids) tvdb_nanovdb_file_close(&in);
    free(g2);
    free(g);
}

/* ------------------------------------------------------------------------ */
/*  Finding 7: NanoVDB BLOSC/LZ4 must produce the whole grid                 */
/* ------------------------------------------------------------------------ */

static void test_nanovdb_short_decompression(void) {
#if defined(TVDB_HAVE_BLOSC)
    printf("skip test_nanovdb_short_decompression: system BLOSC framing\n");
#else
    size_t n = 0;
    uint8_t *g = fixture_nano(&n);
    CHECK(g != NULL);
    if (!g) return;
    size_t keep = n - 512; /* all but the last 512 grid bytes */
    int cap = LZ4_compressBound((int)keep);
    uint8_t *buf = (uint8_t *)calloc(1, 16 + 176 + 2 + 8 + 12 + (size_t)cap);
    uint64_t magic = TVDB_NANOVDB_MAGIC_FILE; memcpy(buf, &magic, 8);
    uint32_t ver = (32u << 21) | (6u << 10); memcpy(buf + 8, &ver, 4);
    uint16_t cnt = 1, codec = TVDB_NANOVDB_CODEC_BLOSC;
    memcpy(buf + 12, &cnt, 2); memcpy(buf + 14, &codec, 2);
    size_t pos = 16;
    uint8_t *meta = buf + pos; pos += 176;
    uint64_t gsz = n; memcpy(meta, &gsz, 8);
    uint32_t ns = 2; memcpy(meta + 136, &ns, 4);
    buf[pos++] = 'g'; buf[pos++] = 0;
    size_t start = pos; pos += 8 + 12;
    int c = LZ4_compress_default((const char *)g, (char *)buf + pos, (int)keep, cap);
    pos += (size_t)c;
    uint64_t frame = 12 + (uint64_t)c; memcpy(buf + start, &frame, 8);
    uint64_t enc = pos - start; memcpy(meta + 8, &enc, 8);
    ctr_t ct; ctr_init(&ct);
    tvdb_allocator_t a = ctr_alloc(&ct);
    tvdb_nanovdb_file_t nf;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    tvdb_status_t st = tvdb_nanovdb_file_open_memory(&nf, buf, pos, &a, &e);
    CHECK(st == TVDB_ERROR_DECOMPRESSION_FAILED);
    if (st == TVDB_OK) tvdb_nanovdb_file_close(&nf);
    CHECK(ct.live_count == 0);
    free(buf);
    free(g);
#endif
}

/* ------------------------------------------------------------------------ */
/*  Finding 8: writer reports allocation failures                            */
/* ------------------------------------------------------------------------ */

static void test_writer_reports_oom(void) {
    ctr_t c; ctr_init(&c);
    tvdb_allocator_t a = ctr_alloc(&c);
    tvdb_file_t f;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    if (tvdb_file_open(&f, g_fixture, &a, &e) != TVDB_OK ||
        tvdb_read_all_grids(&f, &e) != TVDB_OK) {
        CHECK(!"fixture did not load");
        tvdb_file_close(&f);
        return;
    }
    uint8_t *out = NULL; size_t n = 0;
    CHECK(tvdb_write_to_memory(&f, 0, 0, &out, &n, &e) == TVDB_OK);
    /* The returned buffer is exactly *out_size bytes for the allocator. */
    if (out) ctr_free(out, n, &c);
    CHECK(c.mismatches == 0);

    /* Output buffer cannot grow past 64 KiB. */
    c.realloc_limit = 65536;
    out = NULL; n = 0;
    tvdb_status_t st = tvdb_write_to_memory(&f, 0, 0, &out, &n, &e);
    CHECK(st == TVDB_ERROR_OUT_OF_MEMORY);
    CHECK(out == NULL && n == 0);
    if (out) ctr_free(out, n, &c);
    c.realloc_limit = 0;

    /* The "<type>_HalfFloat" string allocation fails. */
    f.grids[0].descriptor.save_float_as_half = 1;
    c.fail_size = strlen(f.grids[0].descriptor.grid_type) + 11;
    out = NULL; n = 0;
    st = tvdb_write_to_memory(&f, 0, 0, &out, &n, &e);
    CHECK(st == TVDB_ERROR_OUT_OF_MEMORY);
    if (out) ctr_free(out, n, &c);
    c.fail_size = 0;
    f.grids[0].descriptor.save_float_as_half = 0;

    tvdb_file_close(&f);
    CHECK(c.live_count == 0 && c.mismatches == 0);
}

/* ------------------------------------------------------------------------ */
/*  Finding 9: _HalfFloat Vec3s / double / Vec3d grids                       */
/* ------------------------------------------------------------------------ */

static void test_half_nonfloat_grids(void) {
    uint8_t mask[64];
    memset(mask, 0, sizeof(mask));
    mask[0] = 0x0f; /* voxels 0..3 active */
    for (int kind = 0; kind < 3; ++kind) {
        /* kind 0: vec3s, 1: double, 2: vec3d */
        static const char *types[3] = { "Tree_vec3s_5_4_3_HalfFloat",
                                        "Tree_double_5_4_3_HalfFloat",
                                        "Tree_vec3d_5_4_3_HalfFloat" };
        size_t comps = kind == 1 ? 1 : 3;
        size_t elem = 2 * comps;
        uint8_t bg[24];
        memset(bg, 0, sizeof(bg));
        if (kind == 1) { double d = 0.5; memcpy(bg, &d, 8); }
        size_t bg_size = kind == 0 ? 12 : kind == 1 ? 8 : 24;
        uint8_t vals[512 * 6];
        memset(vals, 0, sizeof(vals));
        for (int i = 0; i < 512; ++i)
            for (size_t cc = 0; cc < comps; ++cc) {
                uint16_t h = f2h(i < 4 ? (float)(i + 1) + 0.25f * (float)cc : 0.0f);
                memcpy(vals + (size_t)i * elem + cc * 2, &h, 2);
            }
        bb_t p = { 0 };
        put_grid_prefix(&p, 224, 0);
        put_chain(&p, bg, bg_size, elem, mask, vals);
        bb_t file = make_file(224, "h", 1, types[kind], &p);

        for (int pass = 0; pass < 2; ++pass) {
            ctr_t c; ctr_init(&c);
            tvdb_allocator_t a = ctr_alloc(&c);
            tvdb_file_t f;
            tvdb_error_t e; memset(&e, 0, sizeof(e));
            tvdb_status_t st = open_read(&f, &file, &a, &e);
            CHECK(st == TVDB_OK);
            CHECK(f.num_grids == 1 && f.grids[0].tree.num_nodes == 4);
            if (st == TVDB_OK && f.num_grids == 1 &&
                f.grids[0].tree.num_nodes == 4) {
                const tvdb_leaf_node_t *lf = &f.grids[0].tree.nodes[3].u.leaf;
                int bad = 0;
                for (int i = 0; i < 4; ++i)
                    for (size_t cc = 0; cc < comps; ++cc) {
                        double want = (double)(i + 1) + 0.25 * (double)cc, got;
                        if (kind == 0) {
                            float fv; memcpy(&fv, lf->data + (size_t)i * 12 + cc * 4, 4);
                            got = fv;
                        } else {
                            memcpy(&got, lf->data + ((size_t)i * comps + cc) * 8, 8);
                        }
                        bad += got != want;
                    }
                CHECK(bad == 0);
                if (kind == 1) {
                    double bgv = f.grids[0].tree.nodes[0].u.root.background.u.d;
                    CHECK(bgv == 0.5);
                }
                /* Round-trip through the writer keeps the _HalfFloat form. */
                if (pass == 0) {
                    uint8_t *out = NULL; size_t n = 0;
                    CHECK(tvdb_write_to_memory(&f, TVDB_COMPRESS_ACTIVE_MASK |
                                               TVDB_COMPRESS_BLOSC, 0,
                                               &out, &n, &e) == TVDB_OK);
                    if (out) {
                        bb_free(&file);
                        file.d = (uint8_t *)malloc(n);
                        memcpy(file.d, out, n);
                        file.n = file.cap = n;
                        CHECK(contains(file.d, file.n, "_HalfFloat"));
                        CHECK(meta_half_flag(file.d, file.n) == 1);
                        ctr_free(out, n, &c);
                    }
                }
            }
            tvdb_file_close(&f);
            CHECK(c.live_count == 0 && c.mismatches == 0);
        }
        bb_free(&file); bb_free(&p);
    }

    /* OpenVDB takes the half setting from the grid's "is_saved_as_half_float"
     * metadata, so a grid saved as half needs that entry set to true (the
     * fixture has none), and a full-precision grid must not claim it. */
    tvdb_file_t f;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    if (tvdb_file_open(&f, g_fixture, NULL, &e) == TVDB_OK &&
        tvdb_read_all_grids(&f, &e) == TVDB_OK) {
        uint8_t *out = NULL; size_t n = 0;
        f.grids[0].descriptor.save_float_as_half = 1;
        CHECK(tvdb_write_to_memory(&f, TVDB_COMPRESS_ACTIVE_MASK, 0, &out,
                                   &n, &e) == TVDB_OK);
        if (out) CHECK(meta_half_flag(out, n) == 1);
        free(out);
        f.grids[0].descriptor.save_float_as_half = 0;
        out = NULL;
        CHECK(tvdb_write_to_memory(&f, 0, 0, &out, &n, &e) == TVDB_OK);
        if (out) CHECK(meta_half_flag(out, n) != 1);
        free(out);
    } else {
        CHECK(!"fixture did not load");
    }
    tvdb_file_close(&f);
}

/* ------------------------------------------------------------------------ */
/*  Finding 10: VDB->NanoVDB conversion keeps a readable map                 */
/* ------------------------------------------------------------------------ */

static void test_to_nanovdb_map(void) {
    tvdb_file_t f;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    if (tvdb_file_open(&f, g_fixture, NULL, &e) != TVDB_OK ||
        tvdb_read_all_grids(&f, &e) != TVDB_OK) {
        CHECK(!"fixture did not load");
        tvdb_file_close(&f);
        return;
    }
    tvdb_transform_t *x = &f.grids[0].transform;
    x->type = TVDB_TRANSFORM_UNIFORM_SCALE_TRANSLATE;
    for (int k = 0; k < 3; ++k) {
        x->voxel_size[k] = x->scale_values[k] = 0.5;
        x->translation[k] = 1.0 + k;
    }
    uint8_t *nv = NULL; size_t n = 0;
    CHECK(tvdb_grid_to_nanovdb_float(&f.grids[0], &nv, &n, &e) == TVDB_OK);
    tvdb_nanovdb_file_t nf;
    tvdb_status_t st = nv ? tvdb_nanovdb_file_open_memory(&nf, nv, n, NULL, &e)
                          : TVDB_ERROR_INVALID_DATA;
    CHECK(st == TVDB_OK);
    if (st == TVDB_OK) {
        const tvdb_nanovdb_grid_t *g = &nf.grids[0];
        CHECK(g->voxel_size[0] == 0.5 && g->map[0] == 0.5);
        CHECK(g->map[3] == 1.0 && g->map[7] == 2.0 && g->map[11] == 3.0);
        double w[3];
        tvdb_nanovdb_index_to_world(g, 2, 2, 2, w);
        CHECK(w[0] == 2.0 && w[1] == 3.0 && w[2] == 4.0);
        tvdb_nanovdb_file_close(&nf);
    }
    free(nv);
    tvdb_file_close(&f);
}

/* ------------------------------------------------------------------------ */
/*  Finding 11: NanoVDB validation work is bounded by the input size         */
/* ------------------------------------------------------------------------ */

static void test_nanovdb_aliased_children_bounded(void) {
    size_t n = 0;
    uint8_t *g = fixture_nano(&n);
    CHECK(g != NULL);
    if (!g) return;
    /* Every upper slot -> one lower, every lower slot -> one leaf, every root
     * tile -> one upper; declared node counts UINT32_MAX. */
    uint64_t root; memcpy(&root, g + 672 + 24, 8); root += 672;
    uint32_t tiles; memcpy(&tiles, g + root + 24, 4);
    uint64_t rs = tvdb_nanovdb_root_node_size(1);
    int64_t d; memcpy(&d, g + root + rs + 8, 8);
    uint64_t up = root + (uint64_t)d, lo = 0, lf = 0;
    for (uint32_t k = 0; k < 32768 && !lo; k++)
        if (g[up + 4128 + k / 8] & (1u << (k % 8))) { memcpy(&d, g + up + 8256 + 8ull * k, 8); lo = up + (uint64_t)d; }
    for (uint32_t k = 0; k < 4096 && !lf; k++)
        if (g[lo + 544 + k / 8] & (1u << (k % 8))) { memcpy(&d, g + lo + 1088 + 8ull * k, 8); lf = lo + (uint64_t)d; }
    CHECK(lo && lf);
    if (!lo || !lf) { free(g); return; }
    memset(g + up + 4128, 0xFF, 4096);
    for (uint32_t k = 0; k < 32768; k++) { int64_t r = (int64_t)lo - (int64_t)up; memcpy(g + up + 8256 + 8ull * k, &r, 8); }
    memset(g + lo + 544, 0xFF, 512);
    for (uint32_t k = 0; k < 4096; k++) { int64_t r = (int64_t)lf - (int64_t)lo; memcpy(g + lo + 1088 + 8ull * k, &r, 8); }
    for (uint32_t t = 0; t < tiles; t++) { int64_t r = (int64_t)up - (int64_t)root; memcpy(g + root + rs + 32ull * t + 8, &r, 8); }
    memset(g + 704, 0xFF, 12);
    tvdb_nanovdb_file_t nf;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    clock_t t0 = clock();
    tvdb_status_t st = tvdb_nanovdb_file_open_memory(&nf, g, n, NULL, &e);
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    CHECK(st == TVDB_ERROR_INVALID_DATA);
    CHECK(secs < 2.0);
    if (st == TVDB_OK) tvdb_nanovdb_file_close(&nf);
    free(g);
}

/* ------------------------------------------------------------------------ */
/*  Finding 12: header-sized allocations are bounded before allocating       */
/* ------------------------------------------------------------------------ */

static void test_header_sized_allocations(void) {
    for (int kind = 0; kind < 3; ++kind) {
        bb_t file = { 0 }, p = { 0 };
        if (kind == 0) {          /* grid count 0x7fffffff in a tiny file */
            put_header(&file, 224);
            bb_i32(&file, 0);
            bb_i32(&file, 0x7fffffff);
        } else if (kind == 1) {   /* ZIP chunk size 0x7000000000000000 */
            put_grid_prefix(&p, 224, TVDB_COMPRESS_ZIP);
            bb_f32(&p, 3.0f);
            bb_u32(&p, 0); bb_u32(&p, 1);
            bb_i32(&p, 0); bb_i32(&p, 0); bb_i32(&p, 0);
            bb_mask_slot0(&p, 4096); bb_fill(&p, 0, 4096);
            bb_u8(&p, 6); bb_i64(&p, 0x7000000000000000LL);
            file = make_file(224, "g", 1, "Tree_float_5_4_3", &p);
        } else {                  /* PointIndex leaf with 2^60 indices */
            int32_t zero = 0;
            uint8_t mask[64];
            memset(mask, 0xff, sizeof(mask));
            uint8_t vals[512 * 4];
            memset(vals, 0, sizeof(vals));
            put_grid_prefix(&p, 224, 0);
            put_chain(&p, &zero, 4, 4, mask, vals);
            bb_i64(&p, 0x0fffffffffffffffLL);
            file = make_file(224, "g", 1, "Tree_ptidx32_5_4_3", &p);
        }
        ctr_t c; ctr_init(&c); c.cap_bytes = (size_t)64 << 20;
        tvdb_allocator_t a = ctr_alloc(&c);
        tvdb_file_t f;
        tvdb_error_t e; memset(&e, 0, sizeof(e));
        tvdb_status_t st = open_read(&f, &file, &a, &e);
        if (st != TVDB_ERROR_INVALID_DATA)
            fprintf(stderr, "header-sized kind %d: %s\n", kind, tvdb_status_string(st));
        CHECK(st == TVDB_ERROR_INVALID_DATA);
        tvdb_file_close(&f);
        CHECK(c.live_count == 0 && c.mismatches == 0);
        bb_free(&file); bb_free(&p);
    }
}

/* ------------------------------------------------------------------------ */
/*  Finding 13: error paths release everything; names cannot embed NUL      */
/* ------------------------------------------------------------------------ */

static void test_open_error_paths_release(void) {
    /* File metadata: first entry fine, second truncated. */
    bb_t meta = { 0 };
    put_header(&meta, 224);
    bb_i32(&meta, 2);
    bb_cstr(&meta, "a"); bb_cstr(&meta, "string");
    {
        char xs[100]; memset(xs, 'x', sizeof(xs));
        bb_str(&meta, xs, sizeof(xs));
    }
    bb_cstr(&meta, "b"); bb_cstr(&meta, "int32"); bb_i32(&meta, 4);

    /* Grid name with an embedded NUL. */
    bb_t p = { 0 };
    put_grid_prefix(&p, 224, 0);
    bb_f32(&p, 3.0f); bb_u32(&p, 0); bb_u32(&p, 0);
    bb_t nul = make_file(224, "ab\0cdefgh", 9, "Tree_float_5_4_3", &p);

    /* Second descriptor truncated after a valid first one. */
    bb_t two = make_file(224, "g", 1, "Tree_float_5_4_3", &p);
    two.d[8 + 4 + 4 + 4 + 1 + 36 + 4] = 2; /* grid count := 2 */
    bb_cstr(&two, "second");

    const bb_t *inputs[3] = { &meta, &nul, &two };
    for (int i = 0; i < 3; ++i) {
        for (int via_file = 0; via_file < 2; ++via_file) {
            ctr_t c; ctr_init(&c);
            tvdb_allocator_t a = ctr_alloc(&c);
            tvdb_file_t f;
            tvdb_error_t e; memset(&e, 0, sizeof(e));
            tvdb_status_t st;
            if (via_file) {
#if defined(_WIN32)
                continue;
#else
                char path[] = "/tmp/tvdb_audit_io_XXXXXX";
                const char *tmpdir = getenv("TMPDIR");
                char buf[512];
                snprintf(buf, sizeof(buf), "%s/tvdb_audit_io_XXXXXX",
                         tmpdir && *tmpdir ? tmpdir : "/tmp");
                int fd = mkstemp(buf);
                if (fd < 0) { fd = mkstemp(path); if (fd < 0) continue; memcpy(buf, path, sizeof(path)); }
                CHECK(write(fd, inputs[i]->d, inputs[i]->n) == (ssize_t)inputs[i]->n);
                close(fd);
                st = tvdb_file_open(&f, buf, &a, &e);
                unlink(buf);
#endif
            } else {
                st = tvdb_file_open_memory(&f, inputs[i]->d, inputs[i]->n, &a, &e);
            }
            CHECK(st == TVDB_ERROR_INVALID_DATA);
            /* Failed opens own nothing: no close needed, nothing leaked. */
            CHECK(c.live_count == 0);
            if (st == TVDB_OK) tvdb_file_close(&f);
            CHECK(c.live_count == 0 && c.mismatches == 0);
        }
    }
    bb_free(&meta); bb_free(&nul); bb_free(&two); bb_free(&p);
}

/* ------------------------------------------------------------------------ */
/*  Minor: signed-overflow inputs fail cleanly (UBSan reports pre-fix)       */
/* ------------------------------------------------------------------------ */

static void test_overflowing_header_fields(void) {
    for (int kind = 0; kind < 3; ++kind) {
        bb_t p = { 0 }, file = { 0 };
        if (kind == 2) {
            put_grid_prefix(&p, 224, 0);
            bb_f32(&p, 3.0f); bb_u32(&p, 0); bb_u32(&p, 0);
            file = make_file(224, "g", 1, "Tree_float_99999999999_4_3", &p);
        } else {
            put_grid_prefix(&p, 224, TVDB_COMPRESS_BLOSC);
            bb_f32(&p, 3.0f);
            bb_u32(&p, 0); bb_u32(&p, 1);
            bb_i32(&p, 0); bb_i32(&p, 0); bb_i32(&p, 0);
            bb_mask_slot0(&p, 4096); bb_fill(&p, 0, 4096);
            bb_t fr = { 0 };
            if (kind == 0) {      /* blocksize near INT32_MAX */
                bb_u8(&fr, 2); bb_u8(&fr, 1); bb_u8(&fr, 0x20); bb_u8(&fr, 4);
                bb_i32(&fr, 32768 * 4); bb_i32(&fr, 0x7fffffff); bb_i32(&fr, 64);
                bb_fill(&fr, 0, 48);
            } else {              /* split size INT32_MAX */
                bb_u8(&fr, 2); bb_u8(&fr, 1); bb_u8(&fr, 0x20); bb_u8(&fr, 1);
                bb_i32(&fr, 32768 * 4); bb_i32(&fr, 32768 * 4); bb_i32(&fr, 64);
                bb_i32(&fr, 20); bb_i32(&fr, 0x7fffffff);
                bb_fill(&fr, 0, 64 - fr.n);
            }
            bb_u8(&p, 6); bb_i64(&p, (int64_t)fr.n); bb_put(&p, fr.d, fr.n);
            bb_free(&fr);
            file = make_file(224, "g", 1, "Tree_float_5_4_3", &p);
        }
        ctr_t c; ctr_init(&c);
        tvdb_allocator_t a = ctr_alloc(&c);
        tvdb_file_t f;
        tvdb_error_t e; memset(&e, 0, sizeof(e));
        tvdb_status_t st = open_read(&f, &file, &a, &e);
        CHECK(st != TVDB_OK);
        CHECK(c.peak_bytes < ((size_t)8 << 20));
        tvdb_file_close(&f);
        CHECK(c.live_count == 0 && c.mismatches == 0);
        bb_free(&file); bb_free(&p);
    }
}

/* ------------------------------------------------------------------------ */
/*  Plausible: nanovdb_file_close frees f->buffer once                       */
/* ------------------------------------------------------------------------ */

static void test_nanovdb_close_frees_buffer_once(void) {
    ctr_t c; ctr_init(&c);
    tvdb_nanovdb_file_t f;
    memset(&f, 0, sizeof(f));
    f.alloc = ctr_alloc(&c);
    f.file_size = 64;
    f.buffer = (uint8_t *)ctr_malloc(64, &c);
    tvdb_nanovdb_file_close(&f);
    CHECK(c.frees == 1);
    CHECK(c.live_count == 0);
}

/* ------------------------------------------------------------------------ */
/*  Plausible: every allocation failure is reported (read and write)         */
/* ------------------------------------------------------------------------ */

static void test_allocation_failure_sweep(void) {
    /* Small grid whose leaf needs a selection mask (MASK_AND_TWO_INACTIVE). */
    uint8_t mask[64];
    memset(mask, 0, sizeof(mask));
    mask[0] = 0x0f;
    float vals[512];
    for (int i = 0; i < 512; ++i) vals[i] = i < 4 ? (float)i : (i & 1) ? 7.0f : -3.0f;
    float bg = 3.0f;
    bb_t p = { 0 };
    put_grid_prefix(&p, 224, 0);
    put_chain(&p, &bg, 4, 4, mask, vals);
    bb_t raw = make_file(224, "g", 1, "Tree_float_5_4_3", &p);

    tvdb_file_t f;
    tvdb_error_t e; memset(&e, 0, sizeof(e));
    uint8_t *packed = NULL; size_t packed_n = 0;
    CHECK(open_read(&f, &raw, NULL, &e) == TVDB_OK);
    CHECK(tvdb_write_to_memory(&f, TVDB_COMPRESS_ACTIVE_MASK, 0,
                               &packed, &packed_n, &e) == TVDB_OK);
    tvdb_file_close(&f);
    bb_t in = { packed, packed_n, packed_n };

    int saw_ok = 0;
    for (long k = 0; k < 400 && !saw_ok; ++k) {
        ctr_t c; ctr_init(&c); c.fail_at = k;
        tvdb_allocator_t a = ctr_alloc(&c);
        tvdb_status_t st = open_read(&f, &in, &a, &e);
        CHECK(st == TVDB_OK || st == TVDB_ERROR_OUT_OF_MEMORY);
        if (st == TVDB_OK && f.num_grids == 1 && f.grids[0].tree.num_nodes == 4) {
            const uint8_t *d = f.grids[0].tree.nodes[3].u.leaf.data;
            CHECK(memcmp(d, vals, sizeof(vals)) == 0);
            saw_ok = 1;
        }
        tvdb_file_close(&f);
        CHECK(c.live_count == 0 && c.mismatches == 0);
    }
    CHECK(saw_ok);

    /* Writer: fail each allocation in turn on a loaded grid. */
    ctr_t lc; ctr_init(&lc);
    tvdb_allocator_t la = ctr_alloc(&lc);
    CHECK(open_read(&f, &in, &la, &e) == TVDB_OK);
    saw_ok = 0;
    for (long k = 0; k < 400 && !saw_ok && f.num_grids == 1; ++k) {
        lc.calls = 0; lc.fail_at = k;
        long live = lc.live_count;
        uint8_t *out = NULL; size_t n = 0;
        tvdb_status_t st = tvdb_write_to_memory(&f, TVDB_COMPRESS_ACTIVE_MASK |
                                                TVDB_COMPRESS_ZIP, 0, &out, &n, &e);
        CHECK(st == TVDB_OK || st == TVDB_ERROR_OUT_OF_MEMORY);
        if (st == TVDB_OK) { saw_ok = 1; ctr_free(out, n, &lc); }
        else CHECK(out == NULL);
        CHECK(lc.live_count == live);
    }
    lc.fail_at = -1;
    CHECK(saw_ok);
    tvdb_file_close(&f);
    CHECK(lc.live_count == 0 && lc.mismatches == 0);

    free(packed);
    bb_free(&raw); bb_free(&p);
}

#define T(name) { #name, name }
static const struct { const char *name; void (*fn)(void); } tests[] = {
    T(test_v221_internal_values_by_slot),
    T(test_nanovdb_nonfloat_child_validation),
    T(test_root_counts_bounded),
    T(test_truncated_payloads_rejected),
    T(test_mask_two_inactive_values_roundtrip),
    T(test_nanovdb_incompressible_grid_codec),
    T(test_nanovdb_short_decompression),
    T(test_writer_reports_oom),
    T(test_half_nonfloat_grids),
    T(test_to_nanovdb_map),
    T(test_nanovdb_aliased_children_bounded),
    T(test_header_sized_allocations),
    T(test_open_error_paths_release),
    T(test_overflowing_header_fields),
    T(test_nanovdb_close_frees_buffer_once),
    T(test_allocation_failure_sweep),
};

/* argv[1]: sphere.vdb fixture; optional argv[2]: run only that test. */
int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s sphere.vdb [test_name]\n", argv[0]);
        return 2;
    }
    g_fixture = argv[1];
    for (size_t i = 0; i < sizeof(tests) / sizeof(tests[0]); ++i) {
        if (argc > 2 && strcmp(argv[2], tests[i].name) != 0) continue;
        int before = failures;
        tests[i].fn();
        printf("%s %s\n", failures == before ? "[ok]  " : "[FAIL]", tests[i].name);
    }
    printf("failures=%d\n", failures);
    return failures ? 1 : 0;
}
