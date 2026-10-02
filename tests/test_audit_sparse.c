/* Audit regressions: each case reproduces a defect found in review. */
#include "tinyvdb_autograd.h"
#include "tinyvdb_io.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_sparse_tree.h"
#include "tinyvdb_topology.h"

#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #c); ++failures; } } while (0)

static int near(double a, double b, double tol) { return fabs(a - b) <= tol; }

static uint32_t rng_state = 12345u;
static uint32_t rng(void) {
  rng_state = rng_state * 1664525u + 1013904223u;
  return rng_state >> 8;
}

static void build_template(tvdb_grid_t* tmpl) {
  memset(tmpl, 0, sizeof(*tmpl));
  tmpl->descriptor.grid_type = (char*)"Tree_float_5_4_3";
  tmpl->transform.type = TVDB_TRANSFORM_UNIFORM_SCALE;
  for (int a = 0; a < 3; ++a) {
    tmpl->transform.scale_values[a] = 1.0;
    tmpl->transform.voxel_size[a] = 1.0;
  }
  tmpl->tree.layout.num_levels = 4;
  const int dims[4] = {0, 5, 4, 3};
  for (int l = 0; l < 4; ++l) {
    tmpl->tree.layout.levels[l].log2dim = dims[l];
    tmpl->tree.layout.levels[l].value_type = TVDB_VALUE_FLOAT;
    tmpl->tree.layout.levels[l].node_type =
        l == 0 ? TVDB_NODE_ROOT : l == 3 ? TVDB_NODE_LEAF : TVDB_NODE_INTERNAL;
  }
}

/* Brute-force 6-connected dilation reference over a coordinate list. The value
 * at a voxel is min(own value or background, values of active neighbours);
 * duplicate input coordinates use the first occurrence. */
static int dilate_matches_reference(const tvdb_sparse_grid* in, float bg,
                                    const tvdb_sparse_grid* out) {
  static const int N[7][3] = {{0,0,0},{1,0,0},{-1,0,0},{0,1,0},{0,-1,0},{0,0,1},{0,0,-1}};
  size_t expected = 0;
  /* Candidate set: every input voxel shifted by each stencil offset. Count the
   * distinct candidates and check each against the output. */
  for (size_t i = 0; i < in->count; ++i) {
    for (int k = 0; k < 7; ++k) {
      int x = in->coords[i].x + N[k][0], y = in->coords[i].y + N[k][1], z = in->coords[i].z + N[k][2];
      int seen = 0;
      for (size_t j = 0; j < i && !seen; ++j)
        for (int m = 0; m < 7 && !seen; ++m)
          seen = in->coords[j].x + N[m][0] == x && in->coords[j].y + N[m][1] == y &&
                 in->coords[j].z + N[m][2] == z;
      for (int m = 0; m < k && !seen; ++m)
        seen = in->coords[i].x + N[m][0] == x && in->coords[i].y + N[m][1] == y &&
               in->coords[i].z + N[m][2] == z;
      if (seen) continue;
      ++expected;
      float v = bg;
      for (size_t j = 0; j < in->count; ++j)
        if (in->coords[j].x == x && in->coords[j].y == y && in->coords[j].z == z) { v = in->values[j]; break; }
      for (int m = 1; m < 7; ++m)
        for (size_t j = 0; j < in->count; ++j)
          if (in->coords[j].x == x + N[m][0] && in->coords[j].y == y + N[m][1] &&
              in->coords[j].z == z + N[m][2]) {
            if (in->values[j] < v) v = in->values[j];
            break;
          }
      int found = 0;
      for (size_t o = 0; o < out->count; ++o)
        if (out->coords[o].x == x && out->coords[o].y == y && out->coords[o].z == z) {
          found = 1;
          if (out->values[o] != v) return 0;
        }
      if (!found) return 0;
    }
  }
  return expected == out->count;
}

/* Finding 1: the dilation output table was sized for 8x the input but its 0.7
 * load guard tripped at ~5.6x, while one iteration can emit 7x. */
static void test_dilate_output_capacity(void) {
  for (int n = 1; n <= 40; ++n) {
    tvdb_sparse_grid in, out;
    tvdb_sparse_grid_init(&in); tvdb_sparse_grid_init(&out);
    CHECK(tvdb_sparse_grid_reserve(&in, (size_t)n));
    for (int i = 0; i < n; ++i) {
      in.coords[i] = (tvdb_vec3i){i * 10, 0, 0};
      in.values[i] = -1.0f - (float)i;
    }
    in.count = (size_t)n;
    in.voxel_size = 1.0f;
    int ok = tvdb_dilate_sparse(&in, 3.0f, 1, &out);
    CHECK(ok);
    if (ok) {
      CHECK(out.count == (size_t)(7 * n));
      CHECK(dilate_matches_reference(&in, 3.0f, &out));
    }
    tvdb_sparse_grid_free(&in); tvdb_sparse_grid_free(&out);
  }

  /* Sparse random clusters (with duplicates) against the brute-force reference. */
  for (int trial = 0; trial < 30; ++trial) {
    tvdb_sparse_grid in, out;
    tvdb_sparse_grid_init(&in); tvdb_sparse_grid_init(&out);
    size_t n = 20 + rng() % 60;
    CHECK(tvdb_sparse_grid_reserve(&in, n));
    for (size_t i = 0; i < n; ++i) {
      int spread = trial % 2 ? 40 : 6;
      in.coords[i] = (tvdb_vec3i){(int)(rng() % spread) - spread / 2,
                                  (int)(rng() % spread) - spread / 2,
                                  (int)(rng() % spread) - spread / 2};
      in.values[i] = (float)(rng() % 1000) / 100.0f - 5.0f;
    }
    in.count = n;
    in.voxel_size = 1.0f;
    int ok = tvdb_dilate_sparse(&in, 3.0f, 1, &out);
    CHECK(ok);
    if (ok) CHECK(dilate_matches_reference(&in, 3.0f, &out));
    tvdb_sparse_grid_free(&in); tvdb_sparse_grid_free(&out);
  }

  /* The tree entry point routes through the same step. */
  tvdb_grid_t tmpl; build_template(&tmpl);
  enum { NI = 14 };
  tvdb_vec3i coords[NI]; float values[NI];
  for (int i = 0; i < NI; ++i) { coords[i] = (tvdb_vec3i){i * 10, 0, 0}; values[i] = -1.0f; }
  tvdb_sparse_grid sg = {coords, values, NI, 0, 1.0f, 0, 0, 0};
  tvdb_grid_t grid;
  int built = tvdb_grid_from_sparse_using_template(&tmpl, &sg, "iso", 3.0f, &grid);
  CHECK(built);
  if (built) {
    tvdb_sparse_grid out; tvdb_sparse_grid_init(&out);
    CHECK(tvdb_grid_dilate_topology(&grid, 1, &out));
    CHECK(out.count == 7 * NI);
    tvdb_sparse_grid_free(&out);
    tvdb_grid_destroy_owned(&grid);
  }
}

/* Finding 2: the grid VJP of the clamped trilinear sampler dropped border taps
 * and far points, and both VJPs cast huge/NaN coordinates to int. */
static float sample_fd_grid(tvdb_dense_grid* g, tvdb_vec3f p, size_t i) {
  const float eps = 0.25f, s = g->data[i];
  g->data[i] = s + eps;
  float a = tvdb_sample_trilinear_dense(g, p.x, p.y, p.z);
  g->data[i] = s - eps;
  float b = tvdb_sample_trilinear_dense(g, p.x, p.y, p.z);
  g->data[i] = s;
  return (a - b) / (2.0f * eps);
}

static void test_sample_vjp_matches_clamped_forward(void) {
  /* The reported 4x1x1 cases. */
  float d[4] = {1, 2, 3, 4}, gbuf[4];
  tvdb_dense_grid grid = {4, 1, 1, 0, 0, 0, 1.0f, d};
  tvdb_dense_grid gg = {4, 1, 1, 0, 0, 0, 1.0f, gbuf};
  const struct { float x; int idx; } cases[] = {{0.25f, 0}, {3.75f, 3}, {-3.0f, 0}, {1e20f, 3}, {-1e20f, 0}};
  for (size_t c = 0; c < sizeof cases / sizeof cases[0]; ++c) {
    memset(gbuf, 0, sizeof gbuf);
    tvdb_vec3f p = {cases[c].x, 0.5f, 0.5f};
    float go = 1.0f;
    tvdb_sample_trilinear_dense_vjp_grid(&grid, &p, 1, &go, &gg);
    for (int i = 0; i < 4; ++i) {
      CHECK(near(gbuf[i], i == cases[c].idx ? 1.0 : 0.0, 1e-6));
      CHECK(near(gbuf[i], sample_fd_grid(&grid, p, (size_t)i), 1e-5));
    }
    tvdb_vec3f gp = {0, 0, 0};
    tvdb_sample_trilinear_dense_vjp_pts(&grid, &p, 1, &go, &gp);
    CHECK(gp.x == 0.0f && gp.y == 0.0f && gp.z == 0.0f);
  }

  /* 3D grid: grid VJP against finite differences at interior, border and
   * outside points; point VJP against finite differences away from kinks. */
  enum { NX = 4, NY = 3, NZ = 5 };
  float data[NX * NY * NZ], grad[NX * NY * NZ];
  for (int i = 0; i < NX * NY * NZ; ++i) data[i] = sinf((float)i * 0.7f) * 3.0f + (float)i * 0.1f;
  tvdb_dense_grid g3 = {NX, NY, NZ, -1.0f, 0.5f, 2.0f, 0.5f, data};
  tvdb_dense_grid gg3 = {NX, NY, NZ, -1.0f, 0.5f, 2.0f, 0.5f, grad};
  for (int t = 0; t < 200; ++t) {
    /* voxel-index coordinate in [-3, dim + 2], avoiding integer kinks. */
    float v[3]; const int dims[3] = {NX, NY, NZ};
    for (int a = 0; a < 3; ++a) {
      float base = (float)((int)(rng() % (unsigned)(dims[a] + 6)) - 3);
      v[a] = base + 0.1f + 0.8f * (float)(rng() % 1000) / 1000.0f;
    }
    tvdb_vec3f p = {g3.ox + (v[0] + 0.5f) * g3.voxel_size,
                    g3.oy + (v[1] + 0.5f) * g3.voxel_size,
                    g3.oz + (v[2] + 0.5f) * g3.voxel_size};
    float go = 1.5f;
    memset(grad, 0, sizeof grad);
    tvdb_sample_trilinear_dense_vjp_grid(&g3, &p, 1, &go, &gg3);
    double sum = 0.0;
    for (int i = 0; i < NX * NY * NZ; ++i) {
      sum += grad[i];
      CHECK(near(grad[i], go * sample_fd_grid(&g3, p, (size_t)i), 1e-4));
    }
    CHECK(near(sum, go, 1e-4)); /* partition of unity, including outside */

    tvdb_vec3f gp = {0, 0, 0};
    tvdb_sample_trilinear_dense_vjp_pts(&g3, &p, 1, &go, &gp);
    const float e = 1e-3f;
    float fx = (tvdb_sample_trilinear_dense(&g3, p.x + e, p.y, p.z) -
                tvdb_sample_trilinear_dense(&g3, p.x - e, p.y, p.z)) / (2 * e);
    float fy = (tvdb_sample_trilinear_dense(&g3, p.x, p.y + e, p.z) -
                tvdb_sample_trilinear_dense(&g3, p.x, p.y - e, p.z)) / (2 * e);
    float fz = (tvdb_sample_trilinear_dense(&g3, p.x, p.y, p.z + e) -
                tvdb_sample_trilinear_dense(&g3, p.x, p.y, p.z - e)) / (2 * e);
    CHECK(near(gp.x, go * fx, 2e-2));
    CHECK(near(gp.y, go * fy, 2e-2));
    CHECK(near(gp.z, go * fz, 2e-2));
  }

  /* Nonfinite and huge points: no UB, no contribution (forward is constant). */
  tvdb_vec3f bad[3] = {{NAN, 0, 0}, {INFINITY, 0, 0}, {1e30f, -1e30f, 3e38f}};
  float go3[3] = {1, 1, 1};
  tvdb_vec3f gp3[3] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
  memset(grad, 0, sizeof grad);
  tvdb_sample_trilinear_dense_vjp_grid(&g3, bad, 2, go3, &gg3);
  for (int i = 0; i < NX * NY * NZ; ++i) CHECK(grad[i] == 0.0f);
  tvdb_sample_trilinear_dense_vjp_grid(&g3, bad + 2, 1, go3, &gg3);
  double sum = 0.0;
  for (int i = 0; i < NX * NY * NZ; ++i) sum += grad[i];
  CHECK(near(sum, 1.0, 1e-6));
  CHECK(grad[((NZ - 1) * NY + 0) * NX + (NX - 1)] == 1.0f); /* clamped corner */
  tvdb_sample_trilinear_dense_vjp_pts(&g3, bad, 3, go3, gp3);
  for (int i = 0; i < 3; ++i) CHECK(gp3[i].x == 0.0f && gp3[i].y == 0.0f && gp3[i].z == 0.0f);
}

/* Finding 3: the sparse conv VJPs formed tap coordinates in int, overflowing
 * near INT32 limits and wrapping onto unrelated voxels. */
static float conv_objective(const tvdb_sparse_grid* in, const float* k, int kx, int ky, int kz,
                            const float* gout) {
  tvdb_sparse_grid out; tvdb_sparse_grid_init(&out);
  float s = 0.0f;
  if (tvdb_sparse_conv3d(in, k, kx, ky, kz, 0.0f, &out))
    for (size_t i = 0; i < out.count; ++i) s += gout[i] * out.values[i];
  else
    s = NAN;
  tvdb_sparse_grid_free(&out);
  return s;
}

static void test_conv_vjp_int32_limits(void) {
  tvdb_sparse_grid in; tvdb_sparse_grid_init(&in);
  CHECK(tvdb_sparse_grid_reserve(&in, 4));
  in.coords[0] = (tvdb_vec3i){INT_MAX, 0, 0}; in.values[0] = 1;
  in.coords[1] = (tvdb_vec3i){INT_MIN, 0, 0}; in.values[1] = 5;
  in.count = 2;
  in.voxel_size = 1.0f;
  float k[3] = {0, 1, 10}, gout[2] = {1, 0}, gin[2] = {0, 0}, gk[3] = {0, 0, 0};
  CHECK(tvdb_sparse_conv3d_vjp_values(&in, gout, k, 3, 1, 1, gin));
  CHECK(tvdb_sparse_conv3d_vjp_kernel(&in, gout, 3, 1, 1, gk));
  CHECK(gin[0] == 1.0f && gin[1] == 0.0f);
  CHECK(gk[0] == 0.0f && gk[1] == 1.0f && gk[2] == 0.0f);

  /* Exact finite differences (the objective is linear) on all three axes at
   * both limits, including taps that land on real voxels. */
  in.coords[0] = (tvdb_vec3i){INT_MAX, INT_MIN, 7}; in.values[0] = 2;
  in.coords[1] = (tvdb_vec3i){INT_MIN, INT_MAX, 7}; in.values[1] = 3;
  in.coords[2] = (tvdb_vec3i){INT_MAX - 1, INT_MIN, 7}; in.values[2] = 4;
  in.coords[3] = (tvdb_vec3i){INT_MIN, INT_MAX, INT_MAX}; in.values[3] = 6;
  in.count = 4;
  float kk[27], go4[4] = {1, 2, -1, 3}, gin4[4] = {0}, gk27[27] = {0};
  for (int i = 0; i < 27; ++i) kk[i] = (float)(i % 5) - 2.0f;
  CHECK(tvdb_sparse_conv3d_vjp_values(&in, go4, kk, 3, 3, 3, gin4));
  CHECK(tvdb_sparse_conv3d_vjp_kernel(&in, go4, 3, 3, 3, gk27));
  float base = conv_objective(&in, kk, 3, 3, 3, go4);
  for (int i = 0; i < 4; ++i) {
    float s = in.values[i];
    in.values[i] = s + 1.0f;
    float d = conv_objective(&in, kk, 3, 3, 3, go4) - base;
    in.values[i] = s;
    CHECK(gin4[i] == d);
  }
  for (int t = 0; t < 27; ++t) {
    float s = kk[t];
    kk[t] = s + 1.0f;
    float d = conv_objective(&in, kk, 3, 3, 3, go4) - base;
    kk[t] = s;
    CHECK(gk27[t] == d);
  }
  tvdb_sparse_grid_free(&in);
}

/* Finding 4: coarsen/refine overwrote (and leaked) `out` before rejecting an
 * output spacing that overflowed or underflowed. */
static void test_coarsen_refine_invalid_spacing_preserves_output(void) {
  float d[8] = {0};
  float prev[4] = {9, 9, 9, 9};
  tvdb_dense_grid in = {2, 2, 2, 0, 0, 0, 3e38f, d};
  tvdb_dense_grid out = {1, 2, 2, 5, 6, 7, 0.5f, prev};
  CHECK(!tvdb_coarsen_grid(&in, 2, &out, NULL));
  CHECK(out.nx == 1 && out.ny == 2 && out.nz == 2 && out.ox == 5 && out.oy == 6 &&
        out.oz == 7 && out.voxel_size == 0.5f && out.data == prev);

  tvdb_dense_grid in2 = {2, 2, 2, 0, 0, 0, 1e-45f, d};
  CHECK(!tvdb_refine_grid(&in2, 4, &out, NULL));
  CHECK(out.nx == 1 && out.ny == 2 && out.nz == 2 && out.ox == 5 && out.oy == 6 &&
        out.oz == 7 && out.voxel_size == 0.5f && out.data == prev);
  CHECK(prev[0] == 9 && prev[3] == 9);

  /* Valid spacing still succeeds. */
  tvdb_dense_grid in3 = {2, 2, 2, 0, 0, 0, 1.0f, d}, ok_out;
  CHECK(tvdb_coarsen_grid(&in3, 2, &ok_out, NULL));
  CHECK(ok_out.nx == 1 && ok_out.voxel_size == 2.0f && ok_out.data);
  free(ok_out.data);
}

/* Plausible finding: the tree builder sorted duplicate coordinates with an
 * unstable qsort, so which value won was unspecified; first must win. */
static void test_tree_builder_duplicate_first_wins(void) {
  tvdb_grid_t tmpl; build_template(&tmpl);
  enum { N = 4000 };
  tvdb_vec3i* coords = malloc(N * sizeof(*coords));
  float* values = malloc(N * sizeof(*values));
  CHECK(coords && values);
  if (!coords || !values) { free(coords); free(values); return; }
  /* 16 distinct coordinates within one leaf, each repeated many times. */
  for (int i = 0; i < N; ++i) {
    int c = (int)(rng() % 16);
    coords[i] = (tvdb_vec3i){c & 3, (c >> 2) & 3, 1};
    values[i] = (float)i;
  }
  tvdb_sparse_grid sg = {coords, values, N, 0, 1.0f, 0, 0, 0};
  tvdb_grid_t grid;
  int built = tvdb_grid_from_sparse_using_template(&tmpl, &sg, "dup", 0.0f, &grid);
  CHECK(built);
  if (built) {
    tvdb_sparse_grid ex; tvdb_sparse_grid_init(&ex);
    CHECK(tvdb_grid_to_sparse(&grid, &ex));
    CHECK(ex.count == 16);
    for (size_t j = 0; j < ex.count; ++j) {
      float first = NAN;
      for (int i = 0; i < N; ++i)
        if (coords[i].x == ex.coords[j].x && coords[i].y == ex.coords[j].y &&
            coords[i].z == ex.coords[j].z) { first = values[i]; break; }
      CHECK(ex.values[j] == first);
    }
    tvdb_sparse_grid_free(&ex);
    tvdb_grid_destroy_owned(&grid);
  }
  free(coords); free(values);
}

int main(int argc, char **argv) {
  (void)argc; (void)argv;
  test_dilate_output_capacity();
  test_sample_vjp_matches_clamped_forward();
  test_conv_vjp_int32_limits();
  test_coarsen_refine_invalid_spacing_preserves_output();
  test_tree_builder_duplicate_first_wins();
  printf("failures=%d\n", failures);
  return failures ? 1 : 0;
}
