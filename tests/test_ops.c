// Smoke tests for tinyvdb_ops / sample / tsdf / topology / ray / sparse.
// Returns non-zero on failure.

#include "tinyvdb_ops.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_tsdf.h"
#include "tinyvdb_topology.h"
#include "tinyvdb_ray.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_mesh.h"

#define _USE_MATH_DEFINES
#include <math.h>
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int g_failures = 0;

#define EXPECT(cond) do { \
  if (!(cond)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); \
    ++g_failures; \
  } \
} while (0)

#define EXPECT_NEAR(a, b, tol) do { \
  double _a = (double)(a), _b = (double)(b); \
  if (fabs(_a - _b) > (double)(tol)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s (= %g) ~= %s (= %g) within %g\n", \
            __FILE__, __LINE__, #a, _a, #b, _b, (double)(tol)); \
    ++g_failures; \
  } \
} while (0)

// Build a sphere SDF on a dense grid centered at the grid midpoint, radius r voxels.
static void make_sphere_sdf(tvdb_dense_grid* g, int n, float voxel_size, float radius_w) {
  tvdb_dense_grid_init(g, n, n, n);
  g->voxel_size = voxel_size;
  g->ox = g->oy = g->oz = -0.5f * (float)n * voxel_size;
  float cx = 0.0f, cy = 0.0f, cz = 0.0f;
  for (int iz = 0; iz < n; ++iz) {
    for (int iy = 0; iy < n; ++iy) {
      for (int ix = 0; ix < n; ++ix) {
        float wx = g->ox + ((float)ix + 0.5f) * voxel_size;
        float wy = g->oy + ((float)iy + 0.5f) * voxel_size;
        float wz = g->oz + ((float)iz + 0.5f) * voxel_size;
        float dx = wx - cx, dy = wy - cy, dz = wz - cz;
        g->data[(size_t)((iz * n + iy) * n + ix)] = sqrtf(dx*dx + dy*dy + dz*dz) - radius_w;
      }
    }
  }
}

// Phase 1: morphology, CSG, filters, measurement
static void test_phase1(void) {
  tvdb_dense_grid g; make_sphere_sdf(&g, 16, 0.1f, 0.5f);

  // Volume of unit-diameter sphere ~ (4/3)*pi*r^3 = (4/3)*pi*0.125 ~= 0.5236
  float vol = tvdb_volume(&g);
  EXPECT_NEAR(vol, 0.5236f, 0.05f);

  // Surface area ~ 4*pi*r^2 = 4*pi*0.25 ~= 3.1416. Zero-crossing estimator
  // is a coarse upper bound for low-res, so accept generous tolerance.
  float sa = tvdb_surface_area(&g);
  EXPECT(sa > 2.5f && sa < 8.0f);

  // Dilate one step -> volume increases.
  tvdb_dense_grid g2; tvdb_dense_grid_init(&g2, 16, 16, 16);
  g2.voxel_size = g.voxel_size;
  g2.ox = g.ox; g2.oy = g.oy; g2.oz = g.oz;
  memcpy(g2.data, g.data, (size_t)16*16*16 * sizeof(float));
  tvdb_dilate(&g2, 1);
  EXPECT(tvdb_volume(&g2) > vol);

  // Erode one step -> volume decreases.
  memcpy(g2.data, g.data, (size_t)16*16*16 * sizeof(float));
  tvdb_erode(&g2, 1);
  EXPECT(tvdb_volume(&g2) < vol);

  // Open(0)/Close(0) are identity.
  memcpy(g2.data, g.data, (size_t)16*16*16 * sizeof(float));
  tvdb_open(&g2, 0);
  for (size_t i = 0; i < (size_t)16*16*16; ++i) {
    EXPECT(g.data[i] == g2.data[i]);
    if (g_failures) break;
  }

  // CSG union of g with itself == g (within tolerance).
  tvdb_dense_grid gu; tvdb_dense_grid_init(&gu, 16, 16, 16);
  gu.voxel_size = g.voxel_size;
  gu.ox = g.ox; gu.oy = g.oy; gu.oz = g.oz;
  tvdb_csg_union(&g, &g, &gu);
  for (size_t i = 0; i < (size_t)16*16*16; ++i) {
    if (fabsf(g.data[i] - gu.data[i]) > 1e-6f) { EXPECT(0); break; }
  }
  tvdb_dense_grid_free(&gu);

  // Mean filter is volume-preserving on closed shapes (approximately).
  memcpy(g2.data, g.data, (size_t)16*16*16 * sizeof(float));
  tvdb_mean_filter(&g2, 1, 1);
  EXPECT_NEAR(tvdb_volume(&g2), vol, 0.1f);

  // Gaussian filter likewise.
  memcpy(g2.data, g.data, (size_t)16*16*16 * sizeof(float));
  tvdb_gaussian_filter(&g2, 1, 1);
  EXPECT_NEAR(tvdb_volume(&g2), vol, 0.1f);

  tvdb_dense_grid_free(&g);
  tvdb_dense_grid_free(&g2);
}

// Phase 2: differential ops, advection, Poisson
static void test_phase2(void) {
  // Build f(x,y,z) = x^2 (in world space). Laplacian = 2.
  int n = 16;
  float vs = 0.5f;
  tvdb_dense_grid f; tvdb_dense_grid_init(&f, n, n, n);
  f.voxel_size = vs;
  f.ox = -0.5f * (float)n * vs;
  f.oy = -0.5f * (float)n * vs;
  f.oz = -0.5f * (float)n * vs;
  for (int iz = 0; iz < n; ++iz)
    for (int iy = 0; iy < n; ++iy)
      for (int ix = 0; ix < n; ++ix) {
        float wx = f.ox + ((float)ix + 0.5f) * vs;
        f.data[(size_t)((iz * n + iy) * n + ix)] = wx * wx;
      }

  // gradient at interior point ~ (2x, 0, 0)
  int mid = n / 2;
  float gx = tvdb_central_diff_x(&f, mid, mid, mid);
  float gy = tvdb_central_diff_y(&f, mid, mid, mid);
  float gz = tvdb_central_diff_z(&f, mid, mid, mid);
  float wx_mid = f.ox + ((float)mid + 0.5f) * vs;
  EXPECT_NEAR(gx, 2.0f * wx_mid, 1e-3f);
  EXPECT_NEAR(gy, 0.0f, 1e-3f);
  EXPECT_NEAR(gz, 0.0f, 1e-3f);

  // laplacian ~ 2 in interior
  tvdb_dense_grid lap; tvdb_dense_grid_init(&lap, n, n, n);
  lap.voxel_size = vs; lap.ox = f.ox; lap.oy = f.oy; lap.oz = f.oz;
  tvdb_laplacian(&f, &lap);
  EXPECT_NEAR(lap.data[(size_t)((mid * n + mid) * n + mid)], 2.0f, 1e-3f);

  // gradient -> divergence ~= laplacian
  tvdb_dense_vec_grid grad; tvdb_dense_vec_grid_init(&grad, n, n, n);
  grad.voxel_size = vs; grad.ox = f.ox; grad.oy = f.oy; grad.oz = f.oz;
  tvdb_gradient(&f, &grad);
  tvdb_dense_grid div; tvdb_dense_grid_init(&div, n, n, n);
  div.voxel_size = vs; div.ox = f.ox; div.oy = f.oy; div.oz = f.oz;
  tvdb_divergence(&grad, &div);
  EXPECT_NEAR(div.data[(size_t)((mid * n + mid) * n + mid)], 2.0f, 5e-3f);

  // ---- Stronger checks ----
  // div(curl(F)) ≈ 0 for smooth F. Use F = (sin(z), sin(x), sin(y)) on world coords.
  tvdb_dense_vec_grid F; tvdb_dense_vec_grid_init(&F, n, n, n);
  F.voxel_size = vs; F.ox = f.ox; F.oy = f.oy; F.oz = f.oz;
  for (int iz = 0; iz < n; ++iz)
    for (int iy = 0; iy < n; ++iy)
      for (int ix = 0; ix < n; ++ix) {
        float wx = F.ox + ((float)ix + 0.5f) * vs;
        float wy = F.oy + ((float)iy + 0.5f) * vs;
        float wz = F.oz + ((float)iz + 0.5f) * vs;
        size_t i = (size_t)((iz * n + iy) * n + ix) * 3u;
        F.data[i + 0] = sinf(wz);
        F.data[i + 1] = sinf(wx);
        F.data[i + 2] = sinf(wy);
      }
  tvdb_dense_vec_grid C; tvdb_dense_vec_grid_init(&C, n, n, n);
  C.voxel_size = vs; C.ox = f.ox; C.oy = f.oy; C.oz = f.oz;
  tvdb_curl(&F, &C);
  tvdb_dense_grid div_curl; tvdb_dense_grid_init(&div_curl, n, n, n);
  div_curl.voxel_size = vs; div_curl.ox = f.ox; div_curl.oy = f.oy; div_curl.oz = f.oz;
  tvdb_divergence(&C, &div_curl);
  // Check at an interior point — boundary clamping makes the identity hold
  // only away from edges.
  float dc = div_curl.data[(size_t)((mid * n + mid) * n + mid)];
  EXPECT_NEAR(dc, 0.0f, 1e-3f);
  tvdb_dense_vec_grid_free(&F);
  tvdb_dense_vec_grid_free(&C);
  tvdb_dense_grid_free(&div_curl);

  // Poisson recovery: build phi(x,y,z) = sin(pi*x/L)*sin(pi*y/L)*sin(pi*z/L)
  // on a grid with phi = 0 on the boundary (matching the solver's clamp-to-edge).
  // rhs = laplacian(phi). Solve and compare interior to phi.
  int N = 16;
  float vsP = 1.0f / (float)N;  // domain length 1.0
  tvdb_dense_grid phi; tvdb_dense_grid_init(&phi, N, N, N);
  phi.voxel_size = vsP; phi.ox = 0.0f; phi.oy = 0.0f; phi.oz = 0.0f;
  // Place voxel centers at i*h + h/2 in [0, 1]; phi vanishes nowhere here, but
  // clamp-to-edge replication makes effective ghost values equal to the edge
  // voxels — which gives a discrete *Neumann*-ish solver, not Dirichlet. So we
  // can't expect bit-for-bit recovery; we just verify the residual shrinks.
  for (int iz = 0; iz < N; ++iz)
    for (int iy = 0; iy < N; ++iy)
      for (int ix = 0; ix < N; ++ix) {
        float wx = (ix + 0.5f) * vsP;
        float wy = (iy + 0.5f) * vsP;
        float wz = (iz + 0.5f) * vsP;
        phi.data[(size_t)((iz * N + iy) * N + ix)] =
            sinf((float)M_PI * wx) * sinf((float)M_PI * wy) * sinf((float)M_PI * wz);
      }
  tvdb_dense_grid rhs; tvdb_dense_grid_init(&rhs, N, N, N);
  rhs.voxel_size = vsP; rhs.ox = 0; rhs.oy = 0; rhs.oz = 0;
  tvdb_laplacian(&phi, &rhs);

  tvdb_dense_grid x; tvdb_dense_grid_init(&x, N, N, N);
  x.voxel_size = vsP; x.ox = 0; x.oy = 0; x.oz = 0;
  for (size_t i = 0; i < (size_t)N*N*N; ++i) x.data[i] = 0.0f;
  int iters = tvdb_solve_poisson(&rhs, &x, 500, 1e-4f);
  EXPECT(iters > 0 && iters <= 500);

  // Verify residual ||L x - rhs|| / ||rhs|| is small.
  tvdb_dense_grid Lx; tvdb_dense_grid_init(&Lx, N, N, N);
  Lx.voxel_size = vsP; Lx.ox = 0; Lx.oy = 0; Lx.oz = 0;
  tvdb_laplacian(&x, &Lx);
  double rr = 0.0, bb = 0.0;
  for (size_t i = 0; i < (size_t)N*N*N; ++i) {
    double d = (double)Lx.data[i] - (double)rhs.data[i];
    rr += d * d;
    bb += (double)rhs.data[i] * (double)rhs.data[i];
  }
  EXPECT(bb > 0.0 && sqrt(rr / bb) < 1e-2);

  tvdb_dense_grid_free(&phi);
  tvdb_dense_grid_free(&rhs);
  tvdb_dense_grid_free(&x);
  tvdb_dense_grid_free(&Lx);

  // Advection conservation: a constant field advected by any velocity remains
  // constant (mass-preserving for semi-Lagrangian on smooth fields).
  tvdb_dense_grid cf; tvdb_dense_grid_init(&cf, n, n, n);
  cf.voxel_size = vs; cf.ox = f.ox; cf.oy = f.oy; cf.oz = f.oz;
  for (size_t i = 0; i < (size_t)n*n*n; ++i) cf.data[i] = 1.5f;
  tvdb_dense_vec_grid Va; tvdb_dense_vec_grid_init(&Va, n, n, n);
  Va.voxel_size = vs; Va.ox = f.ox; Va.oy = f.oy; Va.oz = f.oz;
  // Simple shear field
  for (int iz = 0; iz < n; ++iz)
    for (int iy = 0; iy < n; ++iy)
      for (int ix = 0; ix < n; ++ix) {
        size_t k = (size_t)((iz * n + iy) * n + ix) * 3u;
        Va.data[k + 0] = 0.5f;
        Va.data[k + 1] = -0.3f;
        Va.data[k + 2] = 0.2f;
      }
  tvdb_dense_grid out_adv; tvdb_dense_grid_init(&out_adv, n, n, n);
  out_adv.voxel_size = vs; out_adv.ox = f.ox; out_adv.oy = f.oy; out_adv.oz = f.oz;
  tvdb_advect_semi_lagrangian(&cf, &Va, 0.1f, &out_adv);
  // Constant field stays constant (modulo edge clamp = also 1.5).
  for (size_t i = 0; i < (size_t)n*n*n; ++i) {
    if (fabsf(out_adv.data[i] - 1.5f) > 1e-5f) { EXPECT(0); break; }
  }
  tvdb_dense_grid_free(&cf);
  tvdb_dense_vec_grid_free(&Va);
  tvdb_dense_grid_free(&out_adv);

  tvdb_dense_grid_free(&f);
  tvdb_dense_grid_free(&lap);
  tvdb_dense_grid_free(&div);
  tvdb_dense_vec_grid_free(&grad);
}

// Phase 4: sampling / splat / TSDF / xform
static void test_phase4(void) {
  tvdb_dense_grid g; make_sphere_sdf(&g, 16, 0.1f, 0.5f);

  // Sampling at a voxel center returns the stored value.
  int n = 16; float vs = 0.1f;
  int ix = 8, iy = 8, iz = 8;
  float wx = g.ox + ((float)ix + 0.5f) * vs;
  float wy = g.oy + ((float)iy + 0.5f) * vs;
  float wz = g.oz + ((float)iz + 0.5f) * vs;
  float vs_at_center = g.data[(size_t)((iz * n + iy) * n + ix)];
  float sampled = tvdb_sample_trilinear_dense(&g, wx, wy, wz);
  EXPECT_NEAR(sampled, vs_at_center, 1e-5f);

  // Splat -> sample round trip on a clean grid.
  tvdb_dense_grid sg; tvdb_dense_grid_init(&sg, n, n, n);
  sg.voxel_size = vs;
  sg.ox = g.ox; sg.oy = g.oy; sg.oz = g.oz;
  for (size_t i = 0; i < (size_t)n*n*n; ++i) sg.data[i] = 0.0f;
  // Splat a single point with value 1 at a voxel center.
  tvdb_vec3f pt = { wx, wy, wz };
  float val = 1.0f;
  tvdb_splat_trilinear_dense(&sg, &pt, &val, 1, NULL);
  // Sample it back: should recover ~1 at the same point.
  float r = tvdb_sample_trilinear_dense(&sg, wx, wy, wz);
  EXPECT_NEAR(r, 1.0f, 1e-3f);
  tvdb_dense_grid_free(&sg);

  // Identity xform.
  float Id[12] = { 1,0,0,0, 0,1,0,0, 0,0,1,0 };
  tvdb_vec3f a = {1.0f, 2.0f, 3.0f}, b;
  tvdb_apply_xform(Id, &a, &b, 1);
  EXPECT_NEAR(b.x, 1.0f, 1e-6f);
  EXPECT_NEAR(b.y, 2.0f, 1e-6f);
  EXPECT_NEAR(b.z, 3.0f, 1e-6f);

  // TSDF: synthesize a depth frame of a plane at z=2, fuse, check that
  // the TSDF zero-crossing is at z ~= 2 along a ray.
  int W = 32, H = 32;
  float* depth = (float*)malloc((size_t)W * H * sizeof(float));
  float fx = 32.0f, fy = 32.0f, cx = 16.0f, cy = 16.0f;
  for (int j = 0; j < H; ++j)
    for (int i = 0; i < W; ++i)
      depth[(size_t)j*W + i] = 2.0f;  // plane at z=2 in camera coords
  tvdb_depth_frame fr;
  fr.width = W; fr.height = H;
  fr.depth = depth;
  fr.fx = fx; fr.fy = fy; fr.cx = cx; fr.cy = cy;
  // Identity world<-camera pose.
  float Ipose[12] = {1,0,0,0, 0,1,0,0, 0,0,1,0};
  memcpy(fr.pose, Ipose, sizeof(Ipose));
  fr.trunc_distance = 0.5f;
  fr.depth_min = 0.1f;
  fr.depth_max = 10.0f;

  // 32x32x32 grid centered around z=2.
  tvdb_dense_grid tsdf; tvdb_dense_grid_init(&tsdf, 32, 32, 32);
  tsdf.voxel_size = 0.1f;
  tsdf.ox = -1.6f; tsdf.oy = -1.6f; tsdf.oz = 1.0f;
  for (size_t i = 0; i < (size_t)32*32*32; ++i) tsdf.data[i] = fr.trunc_distance;
  tvdb_dense_grid wgt; tvdb_dense_grid_init(&wgt, 32, 32, 32);
  wgt.voxel_size = 0.1f;
  wgt.ox = tsdf.ox; wgt.oy = tsdf.oy; wgt.oz = tsdf.oz;
  for (size_t i = 0; i < (size_t)32*32*32; ++i) wgt.data[i] = 0.0f;

  bool ok = tvdb_integrate_tsdf(&tsdf, &wgt, &fr);
  EXPECT(ok);

  // Sample TSDF at z=2 along the optical axis: should be ~0.
  float val_at_plane = tvdb_sample_trilinear_dense(&tsdf, 0.0f, 0.0f, 2.0f);
  EXPECT_NEAR(val_at_plane, 0.0f, 0.15f);

  free(depth);
  tvdb_dense_grid_free(&tsdf);
  tvdb_dense_grid_free(&wgt);
  tvdb_dense_grid_free(&g);
}

// Phase 5: topology / pooling
static void test_phase5(void) {
  tvdb_dense_grid g; make_sphere_sdf(&g, 16, 0.1f, 0.5f);

  // Coarsen 2x then refine 2x: result should be similar (coarse approx).
  tvdb_dense_grid c; tvdb_dense_grid_init(&c, 0, 0, 0);
  EXPECT(tvdb_coarsen_grid(&g, 2, &c, NULL));
  EXPECT(c.nx == 8 && c.ny == 8 && c.nz == 8);
  tvdb_dense_grid r; tvdb_dense_grid_init(&r, 0, 0, 0);
  EXPECT(tvdb_refine_grid(&c, 2, &r, NULL));
  EXPECT(r.nx == 16 && r.ny == 16 && r.nz == 16);
  tvdb_dense_grid_free(&c);
  tvdb_dense_grid_free(&r);

  // Avg pool of constant grid is constant.
  tvdb_dense_grid k; tvdb_dense_grid_init(&k, 8, 8, 8);
  k.voxel_size = 1.0f;
  for (size_t i = 0; i < (size_t)8*8*8; ++i) k.data[i] = 3.5f;
  tvdb_dense_grid kp; tvdb_dense_grid_init(&kp, 0, 0, 0);
  tvdb_avg_pool(&k, 2, 2, 2, &kp, NULL);
  EXPECT(kp.nx == 4 && kp.ny == 4 && kp.nz == 4);
  for (size_t i = 0; i < (size_t)4*4*4; ++i) {
    EXPECT_NEAR(kp.data[i], 3.5f, 1e-5f);
    if (g_failures) break;
  }
  tvdb_dense_grid_free(&k);
  tvdb_dense_grid_free(&kp);

  // Clip preserves overlap.
  float bbmin[3] = {-0.4f, -0.4f, -0.4f};
  float bbmax[3] = { 0.4f,  0.4f,  0.4f};
  tvdb_dense_grid cl; tvdb_dense_grid_init(&cl, 0, 0, 0);
  EXPECT(tvdb_clip_grid(&g, bbmin, bbmax, &cl, NULL));
  EXPECT(cl.nx == 8 && cl.ny == 8 && cl.nz == 8);
  tvdb_dense_grid_free(&cl);

  // Prune snaps near-background to background.
  tvdb_dense_grid p; tvdb_dense_grid_init(&p, 4, 4, 4);
  for (size_t i = 0; i < (size_t)4*4*4; ++i) p.data[i] = 1e-4f;
  tvdb_prune_grid(&p, 0.0f, 1e-3f);
  for (size_t i = 0; i < (size_t)4*4*4; ++i) {
    EXPECT(p.data[i] == 0.0f);
    if (g_failures) break;
  }
  tvdb_dense_grid_free(&p);

  tvdb_dense_grid_free(&g);
}

// Phase 6: ray ops
static void test_phase6(void) {
  tvdb_dense_grid g; make_sphere_sdf(&g, 16, 0.1f, 0.5f);

  // Ray going through grid center along +x.
  tvdb_ray ray;
  ray.origin.x = -2.0f; ray.origin.y = 0.0f; ray.origin.z = 0.0f;
  ray.dir.x = 1.0f; ray.dir.y = 0.0f; ray.dir.z = 0.0f;
  ray.tmin = 0.0f; ray.tmax = 4.0f;

  // Voxels along ray: should traverse 16 voxels in x.
  size_t n = tvdb_voxels_along_ray_dense(&g, &ray, NULL, 0);
  EXPECT(n == 16);

  // Uniform samples
  tvdb_vec3f pts[5];
  float ts[5];
  tvdb_uniform_ray_samples(&ray, 5, pts, ts);
  EXPECT_NEAR(ts[0], 0.0f, 1e-6f);
  EXPECT_NEAR(ts[4], 4.0f, 1e-6f);
  EXPECT_NEAR(pts[2].x, 0.0f, 1e-6f);  // midpoint of x in [-2, 2]

  // Segment along ray through sphere of radius 0.5: chord length ~= 1.0.
  float seg[2 * 4];
  size_t pairs = tvdb_segments_along_ray(&g, &ray, 0.0f, 256, seg, 4);
  EXPECT(pairs == 1);
  if (pairs == 1) {
    float length = seg[1] - seg[0];
    EXPECT_NEAR(length, 1.0f, 0.1f);
  }

  // Batched marching cubes on 1 grid -> sphere should produce real triangles.
  tvdb_triangle_mesh m;
  bool ok = tvdb_marching_cubes_batch(&g, 1, 0.0f, &m, NULL);
  EXPECT(ok);
  EXPECT(m.face_count > 0);
  EXPECT(m.vertex_count > 0);
  tvdb_triangle_mesh_free(&m);

  tvdb_dense_grid_free(&g);
}

// Phase 3: sparse
static void test_phase3(void) {
  tvdb_dense_grid g; make_sphere_sdf(&g, 16, 0.1f, 0.5f);

  // Active coords: voxels with f != 0. Use tolerance equal to background.
  tvdb_sparse_grid sp; tvdb_sparse_grid_init(&sp);
  EXPECT(tvdb_dense_to_sparse(&g, 0.0f, 1e10f, &sp));  // huge tol -> empty
  EXPECT(sp.count == 0);

  // Now keep the narrow band: |f| < 0.2.
  tvdb_sparse_grid sb; tvdb_sparse_grid_init(&sb);
  // We want ENABLED if |f - 0.0| > tolerance; the API keeps voxels where
  // |value - background| > tolerance. So invert: active if |f| > tolerance.
  // For "narrow band", we want |f| < band; that's the inverse, so let's
  // use a sentinel background far from any value.
  EXPECT(tvdb_dense_to_sparse(&g, 1e6f, 0.0f, &sb));
  EXPECT(sb.count == (size_t)16*16*16);  // every voxel kept

  // Round trip: sparse -> dense.
  tvdb_dense_grid back; tvdb_dense_grid_init(&back, 16, 16, 16);
  back.voxel_size = g.voxel_size;
  back.ox = g.ox; back.oy = g.oy; back.oz = g.oz;
  EXPECT(tvdb_sparse_to_dense(&sb, 1e6f, &back));
  for (size_t i = 0; i < (size_t)16*16*16; ++i) {
    if (fabsf(back.data[i] - g.data[i]) > 1e-6f) { EXPECT(0); break; }
  }
  tvdb_dense_grid_free(&back);
  tvdb_sparse_grid_free(&sp);
  tvdb_sparse_grid_free(&sb);

  // Sparse CSG: union of two sparse grids over same frame.
  tvdb_sparse_grid a; tvdb_sparse_grid_init(&a);
  a.voxel_size = 1.0f; a.ox = a.oy = a.oz = 0.0f;
  tvdb_sparse_grid b; tvdb_sparse_grid_init(&b);
  b.voxel_size = 1.0f; b.ox = b.oy = b.oz = 0.0f;
  tvdb_sparse_grid_reserve(&a, 4);
  tvdb_sparse_grid_reserve(&b, 4);
  // a has voxel (0,0,0) with value -1
  a.coords[0].x = 0; a.coords[0].y = 0; a.coords[0].z = 0; a.values[0] = -1.0f; a.count = 1;
  // b has voxel (0,0,0) with value -2 (so union should give -2)
  b.coords[0].x = 0; b.coords[0].y = 0; b.coords[0].z = 0; b.values[0] = -2.0f; b.count = 1;
  // and voxel (1,0,0) with value -0.5 (only in b)
  b.coords[1].x = 1; b.coords[1].y = 0; b.coords[1].z = 0; b.values[1] = -0.5f; b.count = 2;

  tvdb_sparse_grid u; tvdb_sparse_grid_init(&u);
  EXPECT(tvdb_csg_union_sparse(&a, &b, 0.0f, &u));
  EXPECT(u.count == 2);
  for (size_t i = 0; i < u.count; ++i) {
    if (u.coords[i].x == 0) EXPECT_NEAR(u.values[i], -2.0f, 1e-6f);
    if (u.coords[i].x == 1) EXPECT_NEAR(u.values[i], -0.5f, 1e-6f);
  }

  // Erode of {(0,0,0),(1,0,0)}: neither has 6 neighbors in the set, so erosion empties.
  tvdb_sparse_grid eroded; tvdb_sparse_grid_init(&eroded);
  EXPECT(tvdb_erode_sparse(&u, 1, &eroded));
  EXPECT(eroded.count == 0);

  // Dilate: should grow.
  tvdb_sparse_grid dilated; tvdb_sparse_grid_init(&dilated);
  EXPECT(tvdb_dilate_sparse(&u, 0.0f, 1, &dilated));
  EXPECT(dilated.count > u.count);

  tvdb_sparse_grid_free(&a);
  tvdb_sparse_grid_free(&b);
  tvdb_sparse_grid_free(&u);
  tvdb_sparse_grid_free(&eroded);
  tvdb_sparse_grid_free(&dilated);
  tvdb_dense_grid_free(&g);
}

int main(void) {
  printf("[Phase 1] morphology / CSG / filters / measurement\n");
  test_phase1();
  printf("[Phase 2] differential ops / advection / Poisson\n");
  test_phase2();
  printf("[Phase 3] sparse representation / CSG / morphology\n");
  test_phase3();
  printf("[Phase 4] sampling / splat / TSDF / xform\n");
  test_phase4();
  printf("[Phase 5] topology / pooling\n");
  test_phase5();
  printf("[Phase 6] ray ops\n");
  test_phase6();

  if (g_failures == 0) {
    printf("\nAll tests passed.\n");
    return 0;
  } else {
    printf("\n%d failure(s).\n", g_failures);
    return 1;
  }
}
