#include "tinyvdb_grid_index.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_ops.h"
#include "tvdb_memory.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_topology.h"
#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #c); ++failures; } } while (0)

static void test_coordinates(void) {
    int32_t active[] = {0,0,0, 2097152,0,0, 0,0,0, INT32_MAX,1,2, INT32_MIN,1,2};
    int32_t query[] = {0,0,0, 2097152,0,0, -2097152,0,0, INT32_MAX,1,2, INT32_MIN,1,2};
    int64_t idx[5]; uint8_t present[5]; int32_t counts[5];
    CHECK(tvdb_ijk_to_index(active, 5, query, 5, idx));
    CHECK(idx[0] == 0 && idx[1] == 1 && idx[2] == -1 && idx[3] == 3 && idx[4] == 4);
    CHECK(tvdb_coords_in_set(active, 5, query, 5, present));
    CHECK(present[0] && present[1] && !present[2] && present[3] && present[4]);
    CHECK(tvdb_neighbor_counts(active, 5, 26, counts));
    for (int i = 0; i < 5; ++i) CHECK(counts[i] == 0);
    CHECK(!tvdb_neighbor_counts(active, 5, 7, counts));
    CHECK(!tvdb_ijk_to_index(NULL, 1, query, 5, idx));
    CHECK(!tvdb_ijk_to_index(active, SIZE_MAX, query, 5, idx));

    float size[3] = {1,1,1}, origin[3] = {0,0,0};
    float points[] = {0,0,0, 2097152,0,0, 0,0,0};
    int32_t *coords = NULL; size_t count = 0;
    CHECK(tvdb_voxelize_points(points, 3, size, origin, &coords, &count));
    CHECK(count == 2 && coords && coords[0] == 0 && coords[3] == 2097152);
    free(coords);
    float bad[] = {NAN, INFINITY, 2147483648.0f}; int32_t converted[3] = {42,42,42};
    tvdb_world_to_ijk(bad, 1, size, origin, converted);
    CHECK(converted[0] == 0 && converted[1] == 0 && converted[2] == 0);
    uint8_t output = 42;
    CHECK(!tvdb_points_in_set(bad, 1, size, origin, active, 5, &output));
    CHECK(output == 42);
    CHECK(!tvdb_voxelize_points(bad, 1, size, origin, &coords, &count));
    CHECK(coords == NULL && count == 0);
    size[0] = NAN;
    CHECK(!tvdb_points_in_set(points, 1, size, origin, active, 5, &output));
}

static void test_sparse(void) {
    tvdb_vec3i ac[] = {{0,0,0}}, bc[] = {{2097152,0,0}};
    float av[] = {-1}, bv[] = {-2};
    tvdb_sparse_grid a = {ac,av,1,0,1,0,0,0}, b = {bc,bv,1,0,1,0,0,0}, out;
    tvdb_sparse_grid_init(&out);
    CHECK(tvdb_csg_union_sparse(&a, &b, 1, &out));
    CHECK(out.count == 2 && out.values[0] == -1 && out.values[1] == -2);
    tvdb_sparse_grid_free(&out);
    tvdb_vec3i edge[] = {{INT32_MAX,0,0}};
    a.coords = edge;
    CHECK(tvdb_dilate_sparse(&a, 1, 1, &out));
    CHECK(out.count == 6);
    tvdb_sparse_grid_free(&out);
    CHECK(tvdb_erode_sparse(&a, 1, &out)); CHECK(out.count == 0);
    tvdb_sparse_grid_free(&out);
    CHECK(!tvdb_sparse_grid_reserve(&a, 2));
    CHECK(tvdb_sparse_grid_reserve(&out, 1));
    out.coords[0] = ac[0]; out.values[0] = av[0]; out.count = 1;
    tvdb_vec3i *saved_coords = out.coords; float *saved_values = out.values;
    CHECK(!tvdb_sparse_grid_reserve(&out, SIZE_MAX));
    CHECK(out.coords == saved_coords && out.values == saved_values && out.capacity == 1 && out.values[0] == -1);
    tvdb_sparse_grid_free(&out);
}

static int cmp_float(const void *a, const void *b) {
    float x = *(const float*)a, y = *(const float*)b;
    return (x > y) - (x < y);
}
static void test_median(void) {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 4, 3, 2);
    float reference[24], old[24], window[27];
    for (int i = 0; i < 24; ++i) g.data[i] = reference[i] = (float)((i * 19) % 23 - 11);
    for (int it = 0; it < 3; ++it) {
        memcpy(old, reference, sizeof(old));
        for (int z = 0; z < 2; ++z) for (int y = 0; y < 3; ++y) for (int x = 0; x < 4; ++x) {
            int n = 0;
            for (int dz = -1; dz <= 1; ++dz) for (int dy = -1; dy <= 1; ++dy) for (int dx = -1; dx <= 1; ++dx) {
                int xx = x+dx, yy = y+dy, zz = z+dz;
                if (xx < 0) xx = 0; if (xx > 3) xx = 3;
                if (yy < 0) yy = 0; if (yy > 2) yy = 2;
                if (zz < 0) zz = 0; if (zz > 1) zz = 1;
                window[n++] = old[(zz*3+yy)*4+xx];
            }
            qsort(window, 27, sizeof(float), cmp_float);
            reference[(z*3+y)*4+x] = window[13];
        }
    }
    tvdb_median_filter(&g, INT_MAX, 1);
    CHECK(g.data[0] == -11);
    tvdb_median_filter(&g, 1, 3);
    CHECK(memcmp(g.data, reference, sizeof(reference)) == 0);
    tvdb_dense_grid_free(&g);
}

static void test_alloc_sizes(void) {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, -1, 2, 2);
    CHECK(!g.data && g.nx == 0);
    tvdb_dense_grid_init(&g, INT_MAX, INT_MAX, INT_MAX);
    CHECK(!g.data && g.nx == 0);
    tvdb_dense_vec_grid v; tvdb_dense_vec_grid_init(&v, INT_MAX, INT_MAX, INT_MAX);
    CHECK(!v.data && v.nx == 0);
    tvdb_dense_grid_d d; tvdb_dense_grid_d_init(&d, INT_MAX, INT_MAX, INT_MAX);
    CHECK(!d.data && d.nx == 0);
    tvdb_arena_allocator_t arena; tvdb_arena_init(&arena, malloc(32), 32);
    CHECK(tvdb_arena_alloc(&arena, 8) != NULL);
    size_t offset = arena.current_offset;
    CHECK(!tvdb_arena_alloc(&arena, SIZE_MAX) && arena.current_offset == offset);
    arena.current_offset = SIZE_MAX;
    CHECK(!tvdb_arena_alloc(&arena, 1) && arena.current_offset == SIZE_MAX);
    tvdb_arena_destroy(&arena);
}
static void test_ops_contract(void) {
    tvdb_dense_grid g, ref; tvdb_dense_grid_init(&g, 3, 2, 2); tvdb_dense_grid_init(&ref, 3, 2, 2);
    for(int i=0;i<12;++i) g.data[i]=(float)(i*i%17);
    tvdb_laplacian(&g,&ref); tvdb_laplacian(&g,&g);
    CHECK(memcmp(g.data,ref.data,12*sizeof(float))==0);
    float saved[12]; memcpy(saved,g.data,sizeof(saved));
    tvdb_dense_grid wrong=g; wrong.nx=2;
    tvdb_laplacian(&g,&wrong); CHECK(memcmp(saved,g.data,sizeof(saved))==0);
    tvdb_gaussian_filter(&g,INT_MAX,1); tvdb_mean_filter(&g,INT_MAX,1);
    CHECK(memcmp(saved,g.data,sizeof(saved))==0);
    g.data[0]=4; g.data[2]=9;
    CHECK(tvdb_sample_trilinear_dense(&g,FLT_MAX,0.5f,0.5f)==9);
    CHECK(tvdb_sample_trilinear_dense(&g,-FLT_MAX,0.5f,0.5f)==4);
    CHECK(tvdb_sample_quadratic_dense(&g,FLT_MAX,0.5f,0.5f)==9);
    CHECK(tvdb_sample_trilinear_dense(&g,NAN,0,0)==0);
    g.ox=NAN; CHECK(tvdb_sample_trilinear_dense(&g,0,0,0)==0); g.ox=0;
    memset(g.data,0,12*sizeof(float)); tvdb_signed_flood_fill(&g,1e-6f);
    for(int i=0;i<12;++i) CHECK(g.data[i]==0);
    tvdb_dense_grid coarse; CHECK(tvdb_coarsen_grid(&g,INT_MAX,&coarse,NULL));
    CHECK(coarse.nx==1 && coarse.ny==1 && coarse.nz==1); tvdb_dense_grid_free(&coarse);
    CHECK(!tvdb_refine_grid(&g,INT_MAX,&coarse,NULL));
    CHECK(!tvdb_coarsen_grid(&g,2,&g,NULL)); CHECK(g.nx==3 && g.data);
    tvdb_dense_vec_grid velocity; tvdb_dense_vec_grid_init(&velocity,3,2,2);
    for(int i=0;i<36;++i) velocity.data[i]=0.3f*sinf((float)i);
    for(int scheme=TVDB_ADVECT_RK1;scheme<=TVDB_ADVECT_BFECC;++scheme) {
      for(int i=0;i<12;++i) g.data[i]=(float)(i*i%17);
      tvdb_advect(&g,&velocity,0.2f,scheme,1,&ref);
      tvdb_advect(&g,&velocity,0.2f,scheme,1,&g);
      CHECK(memcmp(g.data,ref.data,12*sizeof(float))==0);
    }
    tvdb_dense_vec_grid_free(&velocity);
    tvdb_dense_grid_free(&g); tvdb_dense_grid_free(&ref);
    tvdb_sparse_grid a,b,o; tvdb_sparse_grid_init(&a); tvdb_sparse_grid_init(&b); tvdb_sparse_grid_init(&o);
    CHECK(tvdb_sparse_grid_reserve(&a,2)); CHECK(tvdb_sparse_grid_reserve(&b,1));
    a.count=2; a.coords[0]=a.coords[1]=(tvdb_vec3i){0,0,0}; a.values[0]=-1; a.values[1]=-9;
    b.count=1; b.coords[0]=(tvdb_vec3i){1,0,0}; b.values[0]=-2;
    CHECK(tvdb_csg_intersection_sparse(&a,&b,5,&o)); CHECK(o.count==2 && o.values[0]==5 && o.values[1]==5);
    CHECK(tvdb_csg_difference_sparse(&a,&b,5,&o)); CHECK(o.count==2 && o.values[0]==-1 && o.values[1]==5);
    float identity=1; CHECK(tvdb_sparse_conv3d(&a,&identity,1,1,1,0,&a));
    CHECK(a.count==2 && a.values[0]==-1 && a.values[1]==-1);
    tvdb_sparse_grid borrowed=a; borrowed.capacity=0;
    CHECK(!tvdb_sparse_conv3d(&a,&identity,1,1,1,0,&borrowed)); CHECK(a.values[0]==-1);
    tvdb_sparse_grid_free(&a); tvdb_sparse_grid_free(&b); tvdb_sparse_grid_free(&o);
}
/* Defects that were latent rather than loud: a NULL argument that faulted on one
     precision and returned 0 on the other, a wrapped voxel count that read and
     wrote out of bounds, a sentinel written back as if it were a result, a NaN
     quietly turned into a zero, and a sign convention that disagreed between the
     fp32 and fp64 paths. Each of these is a small guard; the point of collecting
     them is that none of them had a test. */
static void test_measure_and_guards(void) {
    /* tvdb_volume_d / tvdb_surface_area_d dereferenced their argument on the
       first line. Their fp32 twins return 0 for NULL, and the test suite only
       ever exercised the twins. */
    CHECK(tvdb_volume_d(NULL) == 0.0);
    CHECK(tvdb_surface_area_d(NULL) == 0.0);
    { tvdb_dense_grid_d gd; memset(&gd, 0, sizeof gd); gd.nx = gd.ny = gd.nz = 4;
      CHECK(tvdb_volume_d(&gd) == 0.0);
      CHECK(tvdb_surface_area_d(&gd) == 0.0);
      gd.voxel_size = 0.5;
      CHECK(tvdb_volume_d(&gd) == 0.0 && tvdb_surface_area_d(&gd) == 0.0); }

    /* A voxel is inside iff strictly negative. tvdb_surface_area used `<= 0`
       while tvdb_volume and both fp64 twins used `< 0`, so a grid containing an
       exact zero got two different answers, and surface_area disagreed with
       volume on identical data. Both must agree with volume now. */
    { tvdb_dense_grid g; tvdb_dense_grid_init(&g, 2, 1, 1);
      g.data[0] = -1.0f; g.data[1] = 0.0f;      /* one edge crosses, through the zero */
      float area = tvdb_surface_area(&g);
      float vol  = tvdb_volume(&g);
      tvdb_dense_grid_d gd; memset(&gd, 0, sizeof gd);
      gd.nx = 2; gd.ny = gd.nz = 1; gd.voxel_size = 1.0;
      gd.data = (double*)malloc(2 * sizeof(double));
      gd.data[0] = -1.0; gd.data[1] = 0.0;
      CHECK(area == tvdb_surface_area_d(&gd));
      CHECK(vol  == (float)tvdb_volume_d(&gd));
      /* One face of area h^2 = 1, and one inside voxel of volume 1. The zero is
         not inside, so it does not add a second crossing. */
      CHECK(area == 1.0f);
      CHECK(vol == 1.0f);
      free(gd.data);
      tvdb_dense_grid_free(&g); }

    /* tvdb_prune_grid computed (size_t)nx*ny*nz behind only `g && g->data`, so a
       negative extent wrapped to a huge count and the loop ran off the buffer in
       both directions. */
    { tvdb_dense_grid g; memset(&g, 0, sizeof g);
      g.nx = -1; g.ny = 4; g.nz = 4; g.voxel_size = 1.0f;
      g.data = (float*)malloc(16 * sizeof(float));
      for (int i = 0; i < 16; ++i) g.data[i] = 0.0f;
      tvdb_prune_grid(&g, 0.0f, 0.5f);          /* must not touch anything */
      for (int i = 0; i < 16; ++i) CHECK(g.data[i] == 0.0f);
      free(g.data);
      tvdb_prune_grid(NULL, 0.0f, 0.5f); }

    /* tvdb_ijk_to_world had no argument checks at all: five unconditional
       dereferences and no overflow guard on n. */
    { float vs[3] = {1,1,1}, org[3] = {0,0,0}; int32_t ijk[3] = {4,5,6};
      float out[3] = {-1,-1,-1};
      tvdb_ijk_to_world(NULL, 1, vs, org, out);
      CHECK(out[0] == -1.0f && out[1] == -1.0f && out[2] == -1.0f);
      tvdb_ijk_to_world(ijk, 1, vs, NULL, out);
      CHECK(out[0] == -1.0f);
      tvdb_ijk_to_world(ijk, 1, vs, org, NULL);
      tvdb_ijk_to_world(ijk, SIZE_MAX, vs, org, out);
      CHECK(out[0] == -1.0f);
      /* And it still works for the ordinary case. */
      tvdb_ijk_to_world(ijk, 1, vs, org, out);
      CHECK(out[0] == 4.5f && out[1] == 5.5f && out[2] == 6.5f);
      /* Round trip with the guarded sibling. */
      int32_t back[3] = {-1,-1,-1};
      tvdb_world_to_ijk(out, 1, vs, org, back);
      CHECK(back[0] == 4 && back[1] == 5 && back[2] == 6); }
}

static void test_nonfinite_vectors(void) {
    tvdb_dense_vec_grid v, w;
    tvdb_dense_vec_grid_init(&v, 2, 1, 1);
    tvdb_dense_vec_grid_init(&w, 2, 1, 1);
    /* A NaN component must survive normalization. The old `m > 0.0f` test was
       false for a NaN magnitude, so the branch took the zero path and a poisoned
       vector came back as all zeros -- indistinguishable from a real zero. */
    v.data[0] = NAN; v.data[1] = 1.0f; v.data[2] = 0.0f;
    tvdb_normalize_vec(&v, &w);
    CHECK(isnan(w.data[0]));
    /* A zero-length vector has no direction and normalizes to zero. */
    v.data[0] = 0.0f; v.data[1] = 0.0f; v.data[2] = 0.0f;
    tvdb_normalize_vec(&v, &w);
    CHECK(w.data[0] == 0.0f && w.data[1] == 0.0f && w.data[2] == 0.0f);
    /* sqrtf(x*x+y*y+z*z) overflowed to +inf above ~1.8e19, and x/inf then wrote
       0 for a large-but-finite vector. Normalized components must stay ~1. */
    v.data[0] = 3.0e19f; v.data[1] = 4.0e19f; v.data[2] = 0.0f;
    tvdb_normalize_vec(&v, &w);
    CHECK(isfinite(w.data[0]) && isfinite(w.data[1]));
    CHECK(fabsf(w.data[0] - 0.6f) < 1e-5f && fabsf(w.data[1] - 0.8f) < 1e-5f);
    CHECK(fabsf(w.data[2]) < 1e-6f);
    /* The magnitude must be finite too, and close to 5e19. */
    tvdb_dense_grid m; tvdb_dense_grid_init(&m, 2, 1, 1);
    v.data[0] = 3.0e19f; v.data[1] = 4.0e19f; v.data[2] = 0.0f;
    tvdb_magnitude(&v, &m);
    CHECK(isfinite(m.data[0]));
    CHECK(fabsf(m.data[0] - 5.0e19f) / 5.0e19f < 1e-5f);
    tvdb_dense_grid_free(&m);
    tvdb_dense_vec_grid_free(&v); tvdb_dense_vec_grid_free(&w);
}

/* Fast sweeping initialises every non-frozen voxel to a 1e30 sentinel and
   propagates outward from the frozen band. When nothing is inside the band there
   is nothing to propagate from, so every voxel keeps the sentinel -- and the
   write-back used to copy it into the caller's grid while returning success. The
   GPU path already leaves such a field untouched, so this also aligns the CPU
   with it. (A truncated budget is NOT a trigger: one sweep direction orders voxels
   so a corner seed reaches the whole grid in a single pass, which is why the first
   version of this test passed even against the broken code.) */
static void test_sweeping_no_seed(void) {
    const int n = 8;
    const size_t nv = (size_t)n * n * n;
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, n, n, n); g.voxel_size = 1.0f;
    /* A uniform positive field: |1.0| > band, so nothing is frozen. */
    for (size_t i = 0; i < nv; ++i) g.data[i] = 1.0f;
    float *before = (float*)malloc(nv * sizeof(float));
    memcpy(before, g.data, nv * sizeof(float));
    tvdb_fast_sweeping(&g, 0.2f, 5, 0.0f);
    /* No sentinel, no nonfinite value: the field is untouched. */
    for (size_t i = 0; i < nv; ++i) {
        CHECK(isfinite(g.data[i]));
        CHECK(fabsf(g.data[i]) < 1e6f);
        CHECK(memcmp(&g.data[i], &before[i], sizeof(float)) == 0);
    }
    tvdb_dense_grid_free(&g);
    free(before);
    /* fp64 twin, same case. */
    tvdb_dense_grid_d gd; memset(&gd, 0, sizeof gd);
    gd.nx = gd.ny = gd.nz = n; gd.voxel_size = 1.0;
    gd.data = (double*)malloc(nv * sizeof(double));
    for (size_t i = 0; i < nv; ++i) gd.data[i] = 1.0;
    tvdb_fast_sweeping_d(&gd, 0.2, 5, 0.0);
    for (size_t i = 0; i < nv; ++i) {
        CHECK(isfinite(gd.data[i]));
        CHECK(fabs(gd.data[i]) < 1e6);
        CHECK(gd.data[i] == 1.0);
    }
    free(gd.data);
    /* And a real seed still solves, so the guard is not simply disabling the op. */
    tvdb_dense_grid_init(&g, n, n, n); g.voxel_size = 1.0f;
    for (size_t i = 0; i < nv; ++i) g.data[i] = 1.0f;
    g.data[0] = -0.1f;
    tvdb_fast_sweeping(&g, 0.2f, 50, 1e-6f);
    CHECK(g.data[0] == -0.1f);
    CHECK(fabsf(g.data[1]) > 0.0f && fabsf(g.data[1]) < 1e6f);
    CHECK(fabsf(g.data[1] - 1.0f) > 1e-3f);   /* it actually moved */
    tvdb_dense_grid_free(&g);
}

int main(void) {
    test_coordinates(); test_sparse(); test_median(); test_alloc_sizes(); test_ops_contract();
    test_measure_and_guards(); test_nonfinite_vectors(); test_sweeping_no_seed();
    return failures != 0;
}
