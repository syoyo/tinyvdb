// JaggedTensor / GridBatch container unit tests.

#include "tinyvdb_jagged.h"
#include "tinyvdb_sparse.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails = 0;
#define EXPECT(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fails; } \
} while (0)
#define NEAR(a, b) (fabsf((a) - (b)) < 1e-5f)

static void fill_grid(tvdb_sparse_grid* g, int base, int n, float vs, float ox) {
  tvdb_sparse_grid_init(g);
  tvdb_sparse_grid_reserve(g, (size_t)n);
  for (int i = 0; i < n; ++i) {
    g->coords[i].x = base + i; g->coords[i].y = base; g->coords[i].z = base - i;
    g->values[i] = (float)(base + i) * 0.5f - 1.0f;
  }
  g->count = (size_t)n;
  g->voxel_size = vs; g->ox = ox; g->oy = ox + 1.0f; g->oz = ox + 2.0f;
}

int main(void) {
  // ---- JaggedTensor: build, accessors, list pointers ----
  {
    float l0[3] = {1.0f, 2.0f, 3.0f};
    float l2[2] = {7.0f, 8.0f};
    const float* lists[3] = {l0, NULL, l2};
    int64_t sizes[3] = {3, 0, 2};
    tvdb_jagged_t jt;
    EXPECT(tvdb_jagged_from_lists(&jt, 3, lists, sizes, 1), "from_lists");
    EXPECT(tvdb_jagged_list_count(&jt) == 3, "list count");
    EXPECT(tvdb_jagged_total(&jt) == 5, "total");
    EXPECT(tvdb_jagged_list_size(&jt, 0) == 3 && tvdb_jagged_list_size(&jt, 1) == 0 &&
           tvdb_jagged_list_size(&jt, 2) == 2, "list sizes");
    int64_t s = 0; float* p = tvdb_jagged_list_ptr(&jt, 2, &s);
    EXPECT(p && s == 2 && NEAR(p[0], 7.0f) && NEAR(p[1], 8.0f), "list ptr");
    EXPECT(tvdb_jagged_list_ptr(&jt, 1, &s) != NULL && s == 0, "empty list ptr");

    // Reductions (channels=1): per-list sum/mean/max/min.
    float sum[3], mean[3], mx[3], mn[3];
    tvdb_jagged_sum(&jt, sum); tvdb_jagged_mean(&jt, mean);
    tvdb_jagged_max(&jt, mx); tvdb_jagged_min(&jt, mn);
    EXPECT(NEAR(sum[0], 6.0f) && NEAR(sum[2], 15.0f) && NEAR(sum[1], 0.0f), "sum");
    EXPECT(NEAR(mean[0], 2.0f) && NEAR(mean[2], 7.5f), "mean");
    EXPECT(NEAR(mx[0], 3.0f) && NEAR(mn[0], 1.0f) && NEAR(mx[2], 8.0f) && NEAR(mn[2], 7.0f), "max/min");
    EXPECT(NEAR(mx[1], 0.0f) && NEAR(mn[1], 0.0f), "empty-list max/min == 0");  // documented behavior
    tvdb_jagged_free(&jt);
  }

  // ---- JaggedTensor: zero-list and empty-part concat edge cases ----
  {
    tvdb_jagged_t z;
    EXPECT(tvdb_jagged_create(&z, 0, NULL, 1), "zero-list create");
    EXPECT(tvdb_jagged_list_count(&z) == 0 && tvdb_jagged_total(&z) == 0, "zero-list shape");
    EXPECT(tvdb_jagged_list_ptr(&z, 0, NULL) == NULL, "zero-list bad index");
    // Concat of zero parts -> empty, channels defaults to 1.
    tvdb_jagged_t cat0;
    EXPECT(tvdb_jagged_concat(&cat0, NULL, 0), "concat 0 parts");
    EXPECT(tvdb_jagged_list_count(&cat0) == 0 && cat0.channels == 1, "concat 0 parts shape");
    // Concat including a part with an empty list.
    float d[2] = {3.0f, 4.0f};
    const float* lp[2] = {d, NULL};
    int64_t lz[2] = {2, 0};
    tvdb_jagged_t P; EXPECT(tvdb_jagged_from_lists(&P, 2, lp, lz, 1), "part w/ empty list");
    const tvdb_jagged_t* parts[1] = {&P};
    tvdb_jagged_t catP;
    EXPECT(tvdb_jagged_concat(&catP, parts, 1), "concat w/ empty list");
    EXPECT(tvdb_jagged_list_count(&catP) == 2 && tvdb_jagged_total(&catP) == 2, "concat empty-list shape");
    EXPECT(tvdb_jagged_list_size(&catP, 1) == 0, "concat preserved empty list");
    tvdb_jagged_free(&z); tvdb_jagged_free(&cat0); tvdb_jagged_free(&P); tvdb_jagged_free(&catP);
  }

  // ---- GridBatch: zero-grid smoke ----
  {
    tvdb_grid_batch_t gb0;
    EXPECT(tvdb_grid_batch_from_grids(&gb0, NULL, 0), "zero-grid batch");
    EXPECT(tvdb_grid_batch_size(&gb0) == 0 && tvdb_grid_batch_total_voxels(&gb0) == 0, "zero-grid shape");
    tvdb_grid_batch_free(&gb0);
  }

  // ---- JaggedTensor: multi-channel + concat ----
  {
    // 2 channels, 2 lists.
    float a[4] = {1, 2, 3, 4};   // 2 elements x 2 ch
    float b[2] = {5, 6};         // 1 element x 2 ch
    const float* la[2] = {a, b};
    int64_t sa[2] = {2, 1};
    tvdb_jagged_t A; EXPECT(tvdb_jagged_from_lists(&A, 2, la, sa, 2), "A 2ch");

    float c[2] = {9, 10};        // 1 element x 2 ch
    const float* lc[1] = {c};
    int64_t sc[1] = {1};
    tvdb_jagged_t C; EXPECT(tvdb_jagged_from_lists(&C, 1, lc, sc, 2), "C 2ch");

    const tvdb_jagged_t* parts[2] = {&A, &C};
    tvdb_jagged_t cat;
    EXPECT(tvdb_jagged_concat(&cat, parts, 2), "concat");
    EXPECT(tvdb_jagged_list_count(&cat) == 3 && tvdb_jagged_total(&cat) == 4 && cat.channels == 2, "concat shape");
    int64_t s; float* p2 = tvdb_jagged_list_ptr(&cat, 2, &s);  // C's only list
    EXPECT(p2 && s == 1 && NEAR(p2[0], 9.0f) && NEAR(p2[1], 10.0f), "concat tail list");
    float* p0 = tvdb_jagged_list_ptr(&cat, 0, &s);
    EXPECT(p0 && s == 2 && NEAR(p0[3], 4.0f), "concat head list");
    tvdb_jagged_free(&A); tvdb_jagged_free(&C); tvdb_jagged_free(&cat);
  }

  // ---- GridBatch: build from grids, views, jagged bridge, spatial query ----
  {
    tvdb_sparse_grid g0, g1, g2;
    fill_grid(&g0, 0, 4, 0.1f, -1.0f);
    fill_grid(&g1, 10, 2, 0.2f, 5.0f);
    fill_grid(&g2, 100, 3, 0.05f, 0.0f);
    tvdb_sparse_grid grids[3] = {g0, g1, g2};

    tvdb_grid_batch_t gb;
    EXPECT(tvdb_grid_batch_from_grids(&gb, grids, 3), "batch from grids");
    EXPECT(tvdb_grid_batch_size(&gb) == 3, "batch size");
    EXPECT(tvdb_grid_batch_total_voxels(&gb) == 9, "batch total");
    EXPECT(tvdb_grid_batch_grid_size(&gb, 1) == 2, "batch grid size");

    // View of grid 1 must match the original grid (coords/values/transform).
    tvdb_sparse_grid v1;
    EXPECT(tvdb_grid_batch_view(&gb, 1, &v1), "view");
    EXPECT(v1.count == 2 && NEAR(v1.voxel_size, 0.2f) && NEAR(v1.ox, 5.0f), "view transform");
    EXPECT(v1.coords[0].x == 10 && NEAR(v1.values[1], g1.values[1]), "view data");

    // View safety: a view (capacity==0) must not be growable, and freeing it must
    // not free the batch's storage (it just resets the view handle).
    EXPECT(v1.capacity == 0, "view capacity 0");
    EXPECT(!tvdb_sparse_grid_reserve(&v1, 100), "reserve refuses a view");
    tvdb_sparse_grid_free(&v1);  // must NOT free into the batch allocation
    EXPECT(v1.coords == NULL && v1.count == 0, "freed view reset");
    EXPECT(gb.coords[gb.offsets[1]].x == 10, "batch storage intact after view free");

    // values_jagged bridge: per-grid offsets + values match.
    tvdb_jagged_t vj;
    EXPECT(tvdb_grid_batch_values_jagged(&gb, &vj), "values_jagged");
    EXPECT(tvdb_jagged_list_count(&vj) == 3 && tvdb_jagged_total(&vj) == 9, "jagged bridge shape");
    int64_t s; float* g2vals = tvdb_jagged_list_ptr(&vj, 2, &s);
    EXPECT(s == 3 && NEAR(g2vals[0], g2.values[0]) && NEAR(g2vals[2], g2.values[2]), "jagged bridge values");

    // Spatial query within a grid (local index, brute-force).
    int32_t q[3] = {11, 10, 9};  // g1's second voxel: base=10,i=1 -> (11,10,9)
    EXPECT(tvdb_grid_batch_ijk_to_index(&gb, 1, q) == 1, "ijk_to_index hit");
    int32_t miss[3] = {999, 0, 0};
    EXPECT(tvdb_grid_batch_ijk_to_index(&gb, 1, miss) == -1, "ijk_to_index miss");
    // Same coord but wrong batch -> not found.
    int32_t q0[3] = {0, 0, 0};  // g0's first voxel
    EXPECT(tvdb_grid_batch_ijk_to_index(&gb, 0, q0) == 0, "ijk_to_index batch0");
    EXPECT(tvdb_grid_batch_ijk_to_index(&gb, 1, q0) == -1, "ijk_to_index wrong batch");

    tvdb_jagged_free(&vj);
    tvdb_grid_batch_free(&gb);
    tvdb_sparse_grid_free(&g0); tvdb_sparse_grid_free(&g1); tvdb_sparse_grid_free(&g2);
  }

  if (fails == 0) { printf("All jagged/grid-batch tests passed.\n"); return 0; }
  printf("%d jagged/grid-batch failure(s).\n", fails);
  return 1;
}
