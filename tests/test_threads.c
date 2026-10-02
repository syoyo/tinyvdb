/* Thread-count invariance.
 *
 * Nothing in the suite asserted this. `rg omp_set_num_threads tests/` matched
 * only the benchmark harness, and no CTest set OMP_NUM_THREADS, so every CPU test
 * ran once at whatever the host default was -- which meant an op whose result
 * depended on how the work happened to be split was free to pass on one machine
 * and be wrong on another.
 *
 * The contract this pins down is the one the parallel kernels are written to
 * honour: `schedule(static)` over a collapsed (iz,iy) pair, each output element a
 * pure function of its own input window. That makes the result independent of the
 * thread count bit for bit, reductions included, because the summation order
 * within a row does not change -- only which thread performs it.
 *
 * The comparison is an exact memcmp, deliberately. A tolerance would hide exactly
 * the reordering bug this test exists to catch; an op that is only approximately
 * thread-independent is a finding to fix, not to paper over here.
 */
#include "tinyvdb_ops.h"
#include "tinyvdb_topology.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_jagged.h"
#include "tinyvdb_grid_index.h"
#include "tinyvdb_mesh.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _OPENMP
#include <omp.h>
#endif

static int failures;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #c); ++failures; } } while (0)

static int wide_threads(void) {
#ifdef _OPENMP
  int m = omp_get_max_threads();
  return m > 2 ? m : 2;
#else
  return 1;
#endif
}
static void use_threads(int n) {
#ifdef _OPENMP
  omp_set_num_threads(n);
#else
  (void)n;
#endif
}

static void fill_values(float* p, size_t count, unsigned seed) {
  for (size_t i = 0; i < count; ++i) {
    unsigned h = (unsigned)i * 2654435761u + seed * 40503u;
    h ^= h >> 13; h *= 1274126177u; h ^= h >> 16;
    p[i] = ((float)(h & 0xffffu) / 32768.0f) - 1.0f;
  }
}

/* A produced result: a byte blob plus its length in floats. Every op under test
 * is expressed as "given this input, produce this blob", which is what makes the
 * two-pass comparison uniform. */
typedef struct { float* p; size_t n; } blob;
static void blob_free(blob* b) { free(b->p); b->p = NULL; b->n = 0; }

/* Run `produce` once at one thread and once at the widest team; report any
 * difference. `label` is what shows up in the failure message. */
static void expect_same(const char* label, blob (*produce)(void* arg), void* arg) {
  blob a = { NULL, 0 }, b = { NULL, 0 };
  use_threads(1);               a = produce(arg);
  use_threads(wide_threads());  b = produce(arg);
  if (a.n != b.n) {
    fprintf(stderr, "thread invariance: %-20s length %zu vs %zu\n", label, a.n, b.n);
    ++failures;
  } else if (a.n && memcmp(a.p, b.p, a.n * sizeof(float)) != 0) {
    size_t f = 0;
    while (f < a.n && memcmp(&a.p[f], &b.p[f], sizeof(float)) == 0) ++f;
    fprintf(stderr, "thread invariance: %-20s differs at element %zu/%zu (%g vs %g)\n",
            label, f, a.n, a.p[f], b.p[f]);
    ++failures;
  }
  blob_free(&a); blob_free(&b);
}

/* ---------------- in-place scalar grid ops ---------------- */
typedef struct { const char* name; void (*fn)(tvdb_dense_grid*); } sop_t;
static void op_dilate(tvdb_dense_grid* g) { tvdb_dilate(g, 2); }
static void op_erode(tvdb_dense_grid* g) { tvdb_erode(g, 2); }
static void op_open(tvdb_dense_grid* g) { tvdb_open(g, 2); }
static void op_close(tvdb_dense_grid* g) { tvdb_close(g, 2); }
static void op_gauss(tvdb_dense_grid* g) { tvdb_gaussian_filter(g, 3, 2); }
static void op_mean(tvdb_dense_grid* g) { tvdb_mean_filter(g, 2, 2); }
static void op_lapf(tvdb_dense_grid* g) { tvdb_laplacian_filter(g, 2); }
static void op_median(tvdb_dense_grid* g) { tvdb_median_filter(g, 2, 2); }
static void op_flood(tvdb_dense_grid* g) { tvdb_signed_flood_fill(g, 0.5f); }
static void op_lap(tvdb_dense_grid* g) { tvdb_laplacian(g, g); }
static void op_compmax(tvdb_dense_grid* g) { tvdb_comp_max(g, g, g); }
static void op_compmin(tvdb_dense_grid* g) { tvdb_comp_min(g, g, g); }
static void op_compsum(tvdb_dense_grid* g) { tvdb_comp_sum(g, g, g); }
static void op_compmul(tvdb_dense_grid* g) { tvdb_comp_mult(g, g, g); }
static void op_prune(tvdb_dense_grid* g) { tvdb_prune_grid(g, -1.0f, 0.2f); }
static void op_sweep(tvdb_dense_grid* g) { tvdb_fast_sweeping(g, 0.3f, 3, 0.0f); }

static const sop_t SOPS[] = {
  {"dilate", op_dilate}, {"erode", op_erode}, {"open", op_open}, {"close", op_close},
  {"gaussian_filter", op_gauss}, {"mean_filter", op_mean}, {"laplacian_filter", op_lapf},
  {"median_filter", op_median}, {"signed_flood_fill", op_flood}, {"laplacian", op_lap},
  {"comp_max", op_compmax}, {"comp_min", op_compmin}, {"comp_sum", op_compsum},
  {"comp_mult", op_compmul}, {"prune_grid", op_prune}, {"fast_sweeping", op_sweep},
};
#define NSOPS ((int)(sizeof SOPS / sizeof SOPS[0]))

static tvdb_dense_grid G;
static size_t GN;
static blob prod_inplace(void* arg) {
  const sop_t* op = (const sop_t*)arg;
  blob b = { NULL, 0 };
  float* orig = G.data;                 /* restore before returning, or the next
                                           op would start from this op's output */
  float* d = (float*)malloc(GN * sizeof(float));
  if (!d) return b;
  memcpy(d, orig, GN * sizeof(float));
  G.data = d;
  op->fn(&G);
  G.data = orig;
  b.p = d; b.n = GN;
  return b;
}

/* ---------------- vec3 ops ---------------- */
static float* VBASE; static size_t VN;
static void op_gradient(tvdb_dense_vec_grid* o) { tvdb_gradient(&G, o); }
static void op_cpt(tvdb_dense_vec_grid* o) { tvdb_cpt(&G, o); }
static void op_curl(tvdb_dense_vec_grid* o) {
  tvdb_dense_vec_grid v; memset(&v, 0, sizeof v);
  v.nx = G.nx; v.ny = G.ny; v.nz = G.nz; v.voxel_size = G.voxel_size;
  v.data = (float*)malloc(VN * 3 * sizeof(float));
  if (!v.data) return;
  memcpy(v.data, VBASE, VN * 3 * sizeof(float));
  tvdb_curl(&v, o);
  free(v.data);
}
static void op_normalize(tvdb_dense_vec_grid* o) {
  tvdb_dense_vec_grid v; memset(&v, 0, sizeof v);
  v.nx = G.nx; v.ny = G.ny; v.nz = G.nz; v.voxel_size = G.voxel_size;
  v.data = (float*)malloc(VN * 3 * sizeof(float));
  if (!v.data) return;
  memcpy(v.data, VBASE, VN * 3 * sizeof(float));
  tvdb_normalize_vec(&v, o);
  free(v.data);
}
static const struct { const char* name; void (*fn)(tvdb_dense_vec_grid*); } VOPS[] = {
  {"gradient", op_gradient}, {"cpt", op_cpt}, {"curl", op_curl}, {"normalize_vec", op_normalize},
};
#define NVOPS ((int)(sizeof VOPS / sizeof VOPS[0]))

static blob prod_vec3(void* arg) {
  const struct { const char* name; void (*fn)(tvdb_dense_vec_grid*); }* op = arg;
  blob b = { NULL, 0 };
  tvdb_dense_vec_grid o; memset(&o, 0, sizeof o);
  o.nx = G.nx; o.ny = G.ny; o.nz = G.nz; o.voxel_size = G.voxel_size;
  o.data = (float*)malloc(VN * 3 * sizeof(float));
  if (!o.data) return b;
  op->fn(&o);
  b.p = o.data; b.n = VN * 3;
  return b;
}

/* ---------------- scalar reductions ---------------- */
static blob prod_reductions(void* arg) {
  (void)arg;
  blob b = { NULL, 0 };
  b.p = (float*)malloc(2 * sizeof(float));
  if (!b.p) return b;
  b.p[0] = tvdb_surface_area(&G);
  b.p[1] = tvdb_volume(&G);
  b.n = 2;
  return b;
}

/* ---------------- topology constructors ---------------- */
static int CVAR;
static blob prod_ctor(void* arg) {
  (void)arg;
  blob b = { NULL, 0 };
  tvdb_dense_grid g; memset(&g, 0, sizeof g);
  static const float bmin[3] = { 0.1f, 0.1f, 0.1f }, bmax[3] = { 0.7f, 0.6f, 0.8f };
  int ok = 0;
  switch (CVAR) {
    case 0: ok = tvdb_coarsen_grid(&G, 2, &g, NULL); break;
    case 1: ok = tvdb_refine_grid(&G, 2, &g, NULL); break;
    case 2: ok = tvdb_resample_grid(&G, G.voxel_size * 0.5f, 1, &g, NULL); break;
    case 3: ok = tvdb_clip_grid(&G, bmin, bmax, &g, NULL); break;
    case 4: tvdb_max_pool(&G, 2, 2, 2, &g, NULL); ok = g.data != NULL; break;
    default: tvdb_avg_pool(&G, 2, 2, 2, &g, NULL); ok = g.data != NULL; break;
  }
  if (ok && g.data) {
    b.n = (size_t)g.nx * g.ny * g.nz;
    b.p = (float*)malloc(b.n * sizeof(float));
    if (b.p) memcpy(b.p, g.data, b.n * sizeof(float));
    else b.n = 0;
  }
  tvdb_dense_grid_free(&g);
  return b;
}

/* ---------------- sparse ops ---------------- */
static tvdb_sparse_grid SIN;
static float SKERN[27];
static blob prod_dilate_sparse(void* arg) {
  (void)arg;
  blob b = { NULL, 0 };
  tvdb_sparse_grid a; tvdb_sparse_grid_init(&a);
  if (!tvdb_dilate_sparse(&SIN, 1.0f, 2, &a)) { tvdb_sparse_grid_free(&a); return b; }
  /* coords and values interleaved so one blob covers both. */
  b.n = a.count * 4;
  b.p = (float*)malloc(b.n * sizeof(float));
  if (b.p) {
    for (size_t i = 0; i < a.count; ++i) {
      b.p[i*4+0] = (float)a.coords[i].x; b.p[i*4+1] = (float)a.coords[i].y;
      b.p[i*4+2] = (float)a.coords[i].z; b.p[i*4+3] = a.values[i];
    }
  } else b.n = 0;
  tvdb_sparse_grid_free(&a);
  return b;
}
static blob prod_erode_sparse(void* arg) {
  (void)arg;
  blob b = { NULL, 0 };
  tvdb_sparse_grid a; tvdb_sparse_grid_init(&a);
  if (!tvdb_erode_sparse(&SIN, 1, &a)) { tvdb_sparse_grid_free(&a); return b; }
  b.n = a.count * 4;
  b.p = (float*)malloc(b.n * sizeof(float));
  if (b.p) for (size_t i = 0; i < a.count; ++i) {
    b.p[i*4+0] = (float)a.coords[i].x; b.p[i*4+1] = (float)a.coords[i].y;
    b.p[i*4+2] = (float)a.coords[i].z; b.p[i*4+3] = a.values[i];
  }
  else b.n = 0;
  tvdb_sparse_grid_free(&a);
  return b;
}
static blob prod_conv_sparse(void* arg) {
  (void)arg;
  blob b = { NULL, 0 };
  tvdb_sparse_grid a; tvdb_sparse_grid_init(&a);
  if (!tvdb_sparse_conv3d(&SIN, SKERN, 3, 3, 3, 0.0f, &a)) { tvdb_sparse_grid_free(&a); return b; }
  b.n = a.count * 4;
  b.p = (float*)malloc(b.n * sizeof(float));
  if (b.p) for (size_t i = 0; i < a.count; ++i) {
    b.p[i*4+0] = (float)a.coords[i].x; b.p[i*4+1] = (float)a.coords[i].y;
    b.p[i*4+2] = (float)a.coords[i].z; b.p[i*4+3] = a.values[i];
  }
  else b.n = 0;
  tvdb_sparse_grid_free(&a);
  return b;
}
static blob prod_dense_to_sparse(void* arg) {
  (void)arg;
  blob b = { NULL, 0 };
  tvdb_dense_grid dg; tvdb_dense_grid_init(&dg, 20, 20, 20); dg.voxel_size = 0.05f;
  for (size_t i = 0; i < 8000; ++i) dg.data[i] = (i % 7 == 0) ? 1.0f : 0.0f;
  tvdb_sparse_grid sp; tvdb_sparse_grid_init(&sp);
  if (tvdb_dense_to_sparse(&dg, 0.0f, 0.5f, &sp)) {
    b.n = sp.count * 4;
    b.p = (float*)malloc(b.n * sizeof(float));
    if (b.p) for (size_t i = 0; i < sp.count; ++i) {
      b.p[i*4+0] = (float)sp.coords[i].x; b.p[i*4+1] = (float)sp.coords[i].y;
      b.p[i*4+2] = (float)sp.coords[i].z; b.p[i*4+3] = sp.values[i];
    }
    else b.n = 0;
  }
  tvdb_sparse_grid_free(&sp); tvdb_dense_grid_free(&dg);
  return b;
}

/* ---------------- jagged ---------------- */
static tvdb_jagged_t JT;
static blob prod_jagged(void* arg) {
  bool (*fn)(const tvdb_jagged_t*, float*) = *(bool (**)(const tvdb_jagged_t*, float*))arg;
  size_t n = (size_t)JT.num_lists * (size_t)JT.channels;
  blob b = { NULL, 0 };
  b.p = (float*)malloc(n * sizeof(float));
  if (b.p && fn(&JT, b.p)) b.n = n;
  else { free(b.p); b.p = NULL; b.n = 0; }
  return b;
}

/* ---------------- grid index ---------------- */
static int32_t *ACT, *QRY; static size_t NA, NQ;
static blob prod_ijk_index(void* arg) { (void)arg; blob b = { NULL, 0 };
  b.p = (float*)malloc(NQ * sizeof(float)); if (!b.p) return b;
  int64_t* t = (int64_t*)malloc(NQ * sizeof(int64_t)); if (!t) { free(b.p); b.p = NULL; return b; }
  if (tvdb_ijk_to_index(ACT, NA, QRY, NQ, t)) { for (size_t i = 0; i < NQ; ++i) b.p[i] = (float)t[i]; b.n = NQ; }
  free(t); return b; }
/* Both write into raw bytes, so the blob length is the element count rounded up to
 * whole floats -- expect_same compares n*sizeof(float) bytes. Getting this wrong
 * compares uninitialised tail bytes and reports a difference that is not there. */
/* coords_in_set writes one byte per query, so the blob is NQ bytes rounded up to
 * whole floats. neighbor_counts writes one int32 per active voxel, so its blob is
 * NA whole floats -- not NA/4, which under-allocates by 4x and smashes the heap. */
static blob prod_coords_in_set(void* arg) { (void)arg; blob b = { NULL, 0 };
  size_t nb = (NQ + 3u) / 4u;
  b.p = (float*)calloc(nb, sizeof(float)); if (!b.p) return b;
  if (tvdb_coords_in_set(ACT, NA, QRY, NQ, (uint8_t*)b.p)) b.n = nb;
  else { free(b.p); b.p = NULL; } return b; }
static blob prod_neighbor_counts(void* arg) { (void)arg; blob b = { NULL, 0 };
  b.p = (float*)calloc(NA, sizeof(float)); if (!b.p) return b;
  if (tvdb_neighbor_counts(ACT, NA, 26, (int32_t*)b.p)) b.n = NA;
  else { free(b.p); b.p = NULL; } return b; }

/* ---------------- mesh_to_sdf ---------------- */
/* Seeds each voxel's nearest-triangle search with the previous voxel's winner, so
 * it is the op most exposed to how the x rows are split. Rows are independent,
 * so the answer must not move with the thread count. */
static tvdb_triangle_mesh MESH;
static blob prod_mesh_to_sdf(void* arg) {
  (void)arg;
  blob b = { NULL, 0 };
  tvdb_dense_grid g; memset(&g, 0, sizeof g);
  if (!tvdb_mesh_to_sdf(&MESH, G.voxel_size, 3.0f * G.voxel_size, &g, NULL)) { tvdb_dense_grid_free(&g); return b; }
  b.n = (size_t)g.nx * g.ny * g.nz;
  b.p = (float*)malloc(b.n * sizeof(float));
  if (b.p) memcpy(b.p, g.data, b.n * sizeof(float));
  else b.n = 0;
  tvdb_dense_grid_free(&g);
  return b;
}

int main(void) {
#ifdef _OPENMP
  omp_set_dynamic(0);
#endif
  const int nx = 24, ny = 19, nz = 27;
  GN = (size_t)nx * ny * nz; VN = GN;
  float* base_s = (float*)malloc(GN * sizeof(float));
  VBASE = (float*)malloc(VN * 3 * sizeof(float));
  if (!(base_s && VBASE)) { fprintf(stderr, "OOM\n"); return 1; }
  fill_values(base_s, GN, 1u);
  fill_values(VBASE, VN * 3, 5u);

  memset(&G, 0, sizeof G);
  G.nx = nx; G.ny = ny; G.nz = nz; G.voxel_size = 0.05f; G.data = base_s;

  for (int i = 0; i < NSOPS; ++i) expect_same(SOPS[i].name, prod_inplace, (void*)&SOPS[i]);
  for (int i = 0; i < NVOPS; ++i) expect_same(VOPS[i].name, prod_vec3, (void*)&VOPS[i]);
  expect_same("surface_area+volume", prod_reductions, NULL);

  static const char* cnames[] = { "coarsen", "refine", "resample", "clip", "max_pool", "avg_pool" };
  for (CVAR = 0; CVAR < 6; ++CVAR) expect_same(cnames[CVAR], prod_ctor, NULL);

  /* Sparse shell: big enough to exercise the hash and the dilation. */
  tvdb_sparse_grid_init(&SIN);
  tvdb_sparse_grid_reserve(&SIN, 8192);
  SIN.voxel_size = 0.05f;
  for (int z = 0; z < 20; ++z) for (int y = 0; y < 20; ++y) for (int x = 0; x < 20; ++x) {
    int d = x - 10, e = y - 10, f = z - 10;
    if (d < 0) d = -d; if (e < 0) e = -e; if (f < 0) f = -f;
    if (e > d) d = e; if (f > d) d = f;
    if (d >= 9 && d <= 10) {
      SIN.coords[SIN.count].x = x; SIN.coords[SIN.count].y = y; SIN.coords[SIN.count].z = z;
      SIN.values[SIN.count] = (float)d - 10.0f;
      ++SIN.count;
    }
  }
  for (int i = 0; i < 27; ++i) SKERN[i] = 1.0f / 27.0f;
  expect_same("dilate_sparse", prod_dilate_sparse, NULL);
  expect_same("erode_sparse", prod_erode_sparse, NULL);
  expect_same("sparse_conv3d", prod_conv_sparse, NULL);
  expect_same("dense_to_sparse", prod_dense_to_sparse, NULL);
  tvdb_sparse_grid_free(&SIN);

  { const int64_t nl = 200, per = 20; const int ch = 7;
    memset(&JT, 0, sizeof JT);
    int64_t sizes[200];
    for (int64_t i = 0; i < nl; ++i) sizes[i] = per;
    CHECK(tvdb_jagged_create(&JT, nl, sizes, ch));
    for (int64_t i = 0; i < nl * per * ch; ++i) JT.data[i] = (float)((i * 37) % 101) * 0.25f - 3.0f;
    typedef bool (*rfn)(const tvdb_jagged_t*, float*);
    static const struct { const char* n; rfn f; } reds[] = {
      {"jagged_sum", tvdb_jagged_sum}, {"jagged_mean", tvdb_jagged_mean},
      {"jagged_max", tvdb_jagged_max}, {"jagged_min", tvdb_jagged_min},
    };
    for (unsigned r = 0; r < sizeof reds / sizeof reds[0]; ++r) {
      rfn f = reds[r].f;
      expect_same(reds[r].n, prod_jagged, &f);
    }
    tvdb_jagged_free(&JT); }

  NA = 20000; NQ = 20000;
  ACT = (int32_t*)malloc(NA * 3 * sizeof(int32_t));
  QRY = (int32_t*)malloc(NQ * 3 * sizeof(int32_t));
  if (ACT && QRY) {
    for (size_t i = 0; i < NA; ++i) {
      ACT[3*i+0] = (int32_t)((i * 7919) % 631);
      ACT[3*i+1] = (int32_t)((i * 104729) % 577);
      ACT[3*i+2] = (int32_t)((i * 1299709) % 523);
    }
    for (size_t i = 0; i < NQ; ++i) {
      QRY[3*i+0] = (int32_t)((i * 31337) % 640);
      QRY[3*i+1] = (int32_t)((i * 69621) % 600);
      QRY[3*i+2] = (int32_t)((i * 15485863) % 550);
    }
    expect_same("ijk_to_index", prod_ijk_index, NULL);
    expect_same("coords_in_set", prod_coords_in_set, NULL);
    expect_same("neighbor_counts", prod_neighbor_counts, NULL);
  } else CHECK(0);
  free(ACT); free(QRY);

  { const int n = 40; size_t nv = (size_t)n * n * n;
    tvdb_dense_grid sdf; tvdb_dense_grid_init(&sdf, n, n, n); sdf.voxel_size = 1.0f / n;
    for (size_t i = 0; i < nv; ++i) {
      int ix = (int)(i % (size_t)n), iy = (int)((i / (size_t)n) % (size_t)n), iz = (int)(i / ((size_t)n * n));
      float x = (ix + 0.5f) / n - 0.5f, y = (iy + 0.5f) / n - 0.5f, z = (iz + 0.5f) / n - 0.5f;
      sdf.data[i] = sqrtf(x * x + y * y + z * z) - 0.3f;
    }
    tvdb_triangle_mesh_init(&MESH);
    if (tvdb_sdf_to_mesh(&sdf, 0.0f, &MESH, NULL)) {
      G.nx = sdf.nx; G.ny = sdf.ny; G.nz = sdf.nz; G.voxel_size = sdf.voxel_size;
      expect_same("mesh_to_sdf", prod_mesh_to_sdf, NULL);
    } else { fprintf(stderr, "mesh_to_sdf: sdf_to_mesh failed\n"); ++failures; }
    tvdb_triangle_mesh_free(&MESH);
    tvdb_dense_grid_free(&sdf);
    G.nx = nx; G.ny = ny; G.nz = nz; G.voxel_size = 0.05f;
  }

  free(base_s); free(VBASE);
#ifdef _OPENMP
  fprintf(stderr, "thread-count invariance: 1 vs %d threads (max %d)\n", wide_threads(), omp_get_max_threads());
#else
  fprintf(stderr, "thread-count invariance: built without OpenMP, single-threaded only\n");
#endif
  if (failures) { printf("thread invariance: %d FAILURE(S)\n", failures); return 1; }
  printf("thread invariance: OK\n");
  return 0;
}