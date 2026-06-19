// Statistics / diagnostics (tinyvdb_stats.h) and dense operators
// (magnitude/normalize/cpt/composite/filters, tinyvdb_ops.h).

#include "tinyvdb_stats.h"
#include "tinyvdb_levelset.h"
#include "tinyvdb_ops.h"
#include "tinyvdb_mesh.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails = 0;
#define EXPECT(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fails; } \
} while (0)

int main(void) {
  // ---- Statistics on a known grid (values = linear index 0..n-1) ----
  {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 10, 10, 10);
    g.voxel_size = 0.1f;
    size_t n = (size_t)g.nx * g.ny * g.nz;  // 1000
    for (size_t i = 0; i < n; ++i) g.data[i] = (float)i;
    tvdb_grid_stats_t s;
    EXPECT(tvdb_grid_statistics(&g, &s), "stats ok");
    EXPECT(s.count == n, "stats count");
    EXPECT(s.min == 0.0 && s.max == 999.0, "stats min/max");
    EXPECT(fabs(s.mean - 499.5) < 1e-6, "stats mean");
    EXPECT(fabs(s.sum - 499500.0) < 1e-3, "stats sum");
    EXPECT(fabs(s.stddev - sqrt((1e6 - 1.0) / 12.0)) < 1e-3, "stats stddev");

    size_t hist[10];
    EXPECT(tvdb_grid_histogram(&g, 0.0, 1000.0, 10, hist), "histogram ok");
    size_t tot = 0; int uniform = 1;
    for (int b = 0; b < 10; ++b) { tot += hist[b]; if (hist[b] != 100) uniform = 0; }
    EXPECT(tot == n, "histogram counts sum to n");
    EXPECT(uniform, "histogram uniform 100/bin");
    tvdb_dense_grid_free(&g);
  }

  // ---- Constant grid: stddev 0 ----
  {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 4, 4, 4);
    size_t n = 64; for (size_t i = 0; i < n; ++i) g.data[i] = 2.5f;
    tvdb_grid_stats_t s; tvdb_grid_statistics(&g, &s);
    EXPECT(s.min == 2.5 && s.max == 2.5 && fabs(s.mean - 2.5) < 1e-6 && s.stddev == 0.0,
           "constant grid stats");
    tvdb_dense_grid_free(&g);
  }

  // ---- check_level_set: clean SDF |grad|~1, damaged (x3) |grad|~3 ----
  {
    float c[3] = { 0.2f, -0.1f, 0.3f };
    tvdb_dense_grid s; tvdb_level_set_sphere(1.0f, c, 0.05f, 3.0f, &s);
    tvdb_level_set_check_t chk;
    EXPECT(tvdb_check_level_set(&s, 0.08, 0.05, &chk), "check_level_set ok");
    EXPECT(chk.band_count > 0, "check_level_set found band");
    EXPECT(fabs(chk.mean_grad_mag - 1.0) < 0.05, "clean SDF mean|grad|~1");
    EXPECT(chk.bad_fraction < 0.05, "clean SDF few bad voxels");

    size_t n = (size_t)s.nx * s.ny * s.nz;
    for (size_t i = 0; i < n; ++i) s.data[i] *= 3.0f;  // damage gradient
    tvdb_level_set_check_t chk2;
    tvdb_check_level_set(&s, 0.08, 0.05, &chk2);
    EXPECT(fabs(chk2.mean_grad_mag - 3.0) < 0.1, "damaged SDF mean|grad|~3");
    EXPECT(chk2.bad_fraction > 0.9, "damaged SDF mostly bad");
    tvdb_dense_grid_free(&s);
  }

  // ---- check_fog_volume: fog valid, raw SDF invalid ----
  {
    float c[3] = { 0, 0, 0 };
    tvdb_dense_grid s; tvdb_level_set_sphere(1.0f, c, 0.05f, 3.0f, &s);
    int valid; double mn, mx;
    EXPECT(tvdb_check_fog_volume(&s, 1e-5, &valid, &mn, &mx), "check_fog ok");
    EXPECT(!valid && mn < 0.0, "raw SDF is not a valid fog volume");

    tvdb_dense_grid fog;
    tvdb_sdf_to_fog_volume(&s, 3.0f, &fog);
    int fv; double fmn, fmx;
    tvdb_check_fog_volume(&fog, 1e-5, &fv, &fmn, &fmx);
    EXPECT(fv && fmn >= -1e-5 && fmx <= 1.0 + 1e-5, "fog volume is valid [0,1]");
    tvdb_dense_grid_free(&s);
    tvdb_dense_grid_free(&fog);
  }

  // ---- Vector operators: magnitude, normalize ----
  {
    tvdb_dense_vec_grid v; tvdb_dense_vec_grid_init(&v, 2, 2, 2);
    size_t nv = 8;
    for (size_t i = 0; i < nv; ++i) { v.data[i*3+0]=3.0f; v.data[i*3+1]=4.0f; v.data[i*3+2]=0.0f; }
    tvdb_dense_grid mag; tvdb_dense_grid_init(&mag, 2, 2, 2);
    tvdb_magnitude(&v, &mag);
    int ok = 1; for (size_t i=0;i<nv;++i) if (fabsf(mag.data[i]-5.0f)>1e-5f) ok=0;
    EXPECT(ok, "magnitude = 5 for (3,4,0)");

    tvdb_dense_vec_grid nrm; tvdb_dense_vec_grid_init(&nrm, 2, 2, 2);
    tvdb_normalize_vec(&v, &nrm);
    EXPECT(fabsf(nrm.data[0]-0.6f)<1e-5f && fabsf(nrm.data[1]-0.8f)<1e-5f, "normalize (3,4,0)");
    // Zero vector -> zero (no NaN).
    for (int c=0;c<3;++c) v.data[c]=0.0f;
    tvdb_normalize_vec(&v, &nrm);
    EXPECT(nrm.data[0]==0.0f && nrm.data[1]==0.0f && nrm.data[2]==0.0f, "normalize zero -> zero");
    tvdb_dense_vec_grid_free(&v); tvdb_dense_grid_free(&mag); tvdb_dense_vec_grid_free(&nrm);
  }

  // ---- cpt: closest point of a sphere SDF lies on the sphere ----
  {
    float c[3] = { 0.2f, -0.1f, 0.3f };
    tvdb_dense_grid s; tvdb_level_set_sphere(1.0f, c, 0.05f, 3.0f, &s);
    tvdb_dense_vec_grid cp; tvdb_dense_vec_grid_init(&cp, s.nx, s.ny, s.nz);
    tvdb_cpt(&s, &cp);
    // For band voxels (away from grid border), |cpt - center| ~ R = 1.
    int checked = 0, bad = 0;
    for (int iz=1; iz<s.nz-1; ++iz)
      for (int iy=1; iy<s.ny-1; ++iy)
        for (int ix=1; ix<s.nx-1; ++ix) {
          size_t i=(size_t)(iz*s.ny+iy)*s.nx+ix;
          if (fabsf(s.data[i]) > 0.1f) continue;        // near surface only
          float dx=cp.data[i*3+0]-c[0], dy=cp.data[i*3+1]-c[1], dz=cp.data[i*3+2]-c[2];
          float r=sqrtf(dx*dx+dy*dy+dz*dz);
          ++checked; if (fabsf(r-1.0f) > 0.06f) ++bad;
        }
    EXPECT(checked > 0 && bad == 0, "cpt maps band voxels onto the sphere");
    tvdb_dense_grid_free(&s); tvdb_dense_vec_grid_free(&cp);
  }

  // ---- Composite ----
  {
    tvdb_dense_grid a, b, r;
    tvdb_dense_grid_init(&a, 2,2,2); tvdb_dense_grid_init(&b, 2,2,2); tvdb_dense_grid_init(&r, 2,2,2);
    for (size_t i=0;i<8;++i) { a.data[i]=(float)i; b.data[i]=(float)(7-i); }
    tvdb_comp_max(&a,&b,&r); EXPECT(r.data[0]==7.0f && r.data[7]==7.0f, "comp_max");
    tvdb_comp_min(&a,&b,&r); EXPECT(r.data[0]==0.0f && r.data[7]==0.0f, "comp_min");
    tvdb_comp_sum(&a,&b,&r); int s7=1; for(size_t i=0;i<8;++i) if(r.data[i]!=7.0f) s7=0; EXPECT(s7,"comp_sum=7");
    tvdb_comp_mult(&a,&b,&r); EXPECT(r.data[3]==a.data[3]*b.data[3], "comp_mult");
    tvdb_dense_grid_free(&a); tvdb_dense_grid_free(&b); tvdb_dense_grid_free(&r);
  }

  // ---- Median filter removes an impulse ----
  {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 5,5,5);
    for (size_t i=0;i<125;++i) g.data[i]=1.0f;
    size_t mid = (size_t)(2*5+2)*5+2; g.data[mid] = 1000.0f;   // central spike
    tvdb_median_filter(&g, 1, 1);
    EXPECT(fabsf(g.data[mid]-1.0f) < 1e-5f, "median removes impulse");
    tvdb_dense_grid_free(&g);
  }

  // ---- Mean-curvature flow shrinks a sphere (volume decreases) ----
  {
    float c[3] = { 0,0,0 };
    tvdb_dense_grid s; tvdb_level_set_sphere(1.0f, c, 0.05f, 3.0f, &s);
    float v0 = tvdb_volume(&s);
    tvdb_mean_curvature_flow(&s, 0.0003f, 8);
    float v1 = tvdb_volume(&s);
    EXPECT(v1 < v0 && v1 > 0.0f, "mean-curvature flow shrinks the sphere");
    tvdb_dense_grid_free(&s);
  }

  if (fails) { fprintf(stderr, "%d FAILURES\n", fails); return 1; }
  printf("All stats/ops tests passed.\n");
  return 0;
}
