// Level-set primitive generators + SDF utilities (tinyvdb_levelset.h).
//
// Each generator fills a dense narrow-band SDF. We recompute the analytic
// signed distance independently and compare it (clamped to the background) at
// every voxel center, then sanity-check the fog/interior-mask utilities.

#include "tinyvdb_levelset.h"
#include "tinyvdb_mesh.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static int fails = 0;
#define EXPECT(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fails; } \
} while (0)

static float clampf(float v, float lo, float hi) {
  return v < lo ? lo : (v > hi ? hi : v);
}
static float minf(float a, float b) { return a < b ? a : b; }
static float maxf(float a, float b) { return a > b ? a : b; }

static inline float at(const tvdb_dense_grid* g, int i, int j, int k) {
  return g->data[(size_t)(k * g->ny + j) * g->nx + i];
}
static inline void wc(const tvdb_dense_grid* g, int i, int j, int k,
                      float* x, float* y, float* z) {
  *x = g->ox + ((float)i + 0.5f) * g->voxel_size;
  *y = g->oy + ((float)j + 0.5f) * g->voxel_size;
  *z = g->oz + ((float)k + 0.5f) * g->voxel_size;
}

// Compare stored grid vs an analytic SDF, clamped to +/- bg. Returns max abs err.
typedef float (*ref_fn)(float, float, float, const void*);
static float check_analytic(const tvdb_dense_grid* g, float bg, ref_fn fn,
                            const void* p, const char* name) {
  float maxerr = 0.0f;
  int neg = 0, pos = 0;
  for (int k = 0; k < g->nz; ++k)
    for (int j = 0; j < g->ny; ++j)
      for (int i = 0; i < g->nx; ++i) {
        float x, y, z; wc(g, i, j, k, &x, &y, &z);
        float ref = clampf(fn(x, y, z, p), -bg, bg);
        float e = fabsf(at(g, i, j, k) - ref);
        if (e > maxerr) maxerr = e;
        if (at(g, i, j, k) < 0.0f) ++neg; else ++pos;
      }
  printf("[%s] %dx%dx%d maxerr=%.3e neg=%d pos=%d\n",
         name, g->nx, g->ny, g->nz, (double)maxerr, neg, pos);
  EXPECT(maxerr < 1e-4f, "analytic SDF mismatch");
  EXPECT(neg > 0 && pos > 0, "expected both interior and exterior voxels");
  return maxerr;
}

typedef struct { float c[3], r; } sph_t;
static float sph_ref(float x, float y, float z, const void* p) {
  const sph_t* s = (const sph_t*)p;
  float dx = x - s->c[0], dy = y - s->c[1], dz = z - s->c[2];
  return sqrtf(dx*dx + dy*dy + dz*dz) - s->r;
}

typedef struct { float c[3], he[3]; } box_t;
static float box_ref(float x, float y, float z, const void* p) {
  const box_t* b = (const box_t*)p;
  float qx = fabsf(x-b->c[0]) - b->he[0];
  float qy = fabsf(y-b->c[1]) - b->he[1];
  float qz = fabsf(z-b->c[2]) - b->he[2];
  float ox=maxf(qx,0), oy=maxf(qy,0), oz=maxf(qz,0);
  return sqrtf(ox*ox+oy*oy+oz*oz) + minf(maxf(qx,maxf(qy,qz)), 0.0f);
}

typedef struct { float c[3], R, r; } tor_t;
static float tor_ref(float x, float y, float z, const void* p) {
  const tor_t* t = (const tor_t*)p;
  float dx=x-t->c[0], dy=y-t->c[1], dz=z-t->c[2];
  float qx = sqrtf(dx*dx+dz*dz) - t->R;
  return sqrtf(qx*qx+dy*dy) - t->r;
}

typedef struct { float a[3], b[3], r; } cap_t;
static float cap_ref(float x, float y, float z, const void* p) {
  const cap_t* c = (const cap_t*)p;
  float bax=c->b[0]-c->a[0], bay=c->b[1]-c->a[1], baz=c->b[2]-c->a[2];
  float pax=x-c->a[0], pay=y-c->a[1], paz=z-c->a[2];
  float baba = bax*bax+bay*bay+baz*baz;
  float h = baba>0 ? clampf((pax*bax+pay*bay+paz*baz)/baba, 0, 1) : 0;
  float dx=pax-bax*h, dy=pay-bay*h, dz=paz-baz*h;
  return sqrtf(dx*dx+dy*dy+dz*dz) - c->r;
}

int main(void) {
  const float vs = 0.1f, hw = 3.0f, bg = hw * vs;

  // ---- Sphere ----
  {
    float c[3] = { 0.3f, -0.2f, 0.5f };
    tvdb_dense_grid g;
    EXPECT(tvdb_level_set_sphere(1.0f, c, vs, hw, &g), "sphere build");
    sph_t s = { { c[0], c[1], c[2] }, 1.0f };
    check_analytic(&g, bg, sph_ref, &s, "sphere");
    // Center voxel deep interior -> clamped to -bg.
    float cx, cy, cz;
    int ci = (int)lroundf((c[0]-g.ox)/vs - 0.5f);
    int cj = (int)lroundf((c[1]-g.oy)/vs - 0.5f);
    int ck = (int)lroundf((c[2]-g.oz)/vs - 0.5f);
    wc(&g, ci, cj, ck, &cx, &cy, &cz);
    EXPECT(fabsf(at(&g, ci, cj, ck) + bg) < 1e-5f, "sphere center == -bg");
    tvdb_dense_grid_free(&g);
  }

  // ---- Box ----
  {
    float c[3] = { 0.0f, 0.0f, 0.0f }, he[3] = { 0.5f, 0.4f, 0.6f };
    tvdb_dense_grid g;
    EXPECT(tvdb_level_set_box(he, c, vs, hw, &g), "box build");
    box_t b = { { 0,0,0 }, { 0.5f, 0.4f, 0.6f } };
    check_analytic(&g, bg, box_ref, &b, "box");
    tvdb_dense_grid_free(&g);
  }

  // ---- Torus ----
  {
    float c[3] = { 0.1f, 0.0f, -0.1f };
    tvdb_dense_grid g;
    EXPECT(tvdb_level_set_torus(1.0f, 0.3f, c, vs, hw, &g), "torus build");
    tor_t t = { { c[0], c[1], c[2] }, 1.0f, 0.3f };
    check_analytic(&g, bg, tor_ref, &t, "torus");
    tvdb_dense_grid_free(&g);
  }

  // ---- Capsule ----
  {
    float p0[3] = { -0.5f, 0.1f, 0.0f }, p1[3] = { 0.5f, 0.1f, 0.2f };
    tvdb_dense_grid g;
    EXPECT(tvdb_level_set_capsule(p0, p1, 0.25f, vs, hw, &g), "capsule build");
    cap_t c = { { p0[0],p0[1],p0[2] }, { p1[0],p1[1],p1[2] }, 0.25f };
    check_analytic(&g, bg, cap_ref, &c, "capsule");
    tvdb_dense_grid_free(&g);
  }

  // ---- sdf_to_fog_volume + interior_mask on a sphere ----
  {
    float c[3] = { 0,0,0 };
    tvdb_dense_grid sdf;
    EXPECT(tvdb_level_set_sphere(1.0f, c, vs, hw, &sdf), "sphere for fog");

    tvdb_dense_grid fog;
    EXPECT(tvdb_sdf_to_fog_volume(&sdf, hw, &fog), "fog build");
    EXPECT(fog.nx == sdf.nx && fog.ny == sdf.ny && fog.nz == sdf.nz, "fog shape");
    int bad = 0; float fmax = 0.0f;
    size_t n = (size_t)sdf.nx * sdf.ny * sdf.nz;
    for (size_t i = 0; i < n; ++i) {
      float f = fog.data[i];
      if (f < -1e-6f || f > 1.0f + 1e-6f) ++bad;             // range [0,1]
      if (sdf.data[i] >= 0.0f && f > 1e-6f) ++bad;           // exterior -> 0
      if (f > fmax) fmax = f;
    }
    EXPECT(bad == 0, "fog values out of range / nonzero outside");
    EXPECT(fmax > 0.99f, "fog deep interior should reach ~1");

    tvdb_dense_grid mask;
    EXPECT(tvdb_sdf_interior_mask(&sdf, 0.0f, &mask), "mask build");
    int m1 = 0, mbad = 0;
    for (size_t i = 0; i < n; ++i) {
      float mv = mask.data[i];
      if (mv != 0.0f && mv != 1.0f) ++mbad;
      if ((mv == 1.0f) != (sdf.data[i] < 0.0f)) ++mbad;
      if (mv == 1.0f) ++m1;
    }
    EXPECT(mbad == 0, "interior mask inconsistent with sdf sign");
    EXPECT(m1 > 0, "interior mask should mark some voxels");

    tvdb_dense_grid_free(&sdf);
    tvdb_dense_grid_free(&fog);
    tvdb_dense_grid_free(&mask);
  }

  // ---- Platonic solids ----
  // Validate geometry without re-deriving face normals: every near-surface
  // voxel must lie between the inscribed sphere (inradius = R*ratio) and the
  // circumscribed sphere (circumradius = R), and the band must reach both.
  {
    struct { int faces; float ratio; const char* name; } solids[] = {
      { 4,  1.0f/3.0f,           "tetrahedron" },
      { 6,  0.57735027f,         "cube" },
      { 8,  0.57735027f,         "octahedron" },
      { 12, 0.79465447f,         "dodecahedron" },
      { 20, 0.79465447f,         "icosahedron" },
    };
    const float R = 1.0f, pvs = 0.05f, phw = 3.0f, pbg = phw * pvs;
    float ctr[3] = { 0.2f, -0.1f, 0.3f };
    for (size_t si = 0; si < sizeof(solids) / sizeof(solids[0]); ++si) {
      tvdb_dense_grid g;
      int ok = tvdb_level_set_platonic(solids[si].faces, R, ctr, pvs, phw, &g);
      EXPECT(ok, "platonic build");
      if (!ok) continue;
      float inrad = R * solids[si].ratio;
      float band = 2.0f * pvs;
      float minz = 1e9f, maxz = -1e9f;
      int neg = 0, pos = 0, outside_circ = 0, near = 0, range_bad = 0;
      for (int k = 0; k < g.nz; ++k)
        for (int j = 0; j < g.ny; ++j)
          for (int i = 0; i < g.nx; ++i) {
            float x, y, z; wc(&g, i, j, k, &x, &y, &z);
            float d = at(&g, i, j, k);
            if (d < -pbg - 1e-5f || d > pbg + 1e-5f) ++range_bad;
            if (d < 0) ++neg; else ++pos;
            float dist = sqrtf((x-ctr[0])*(x-ctr[0]) + (y-ctr[1])*(y-ctr[1]) +
                               (z-ctr[2])*(z-ctr[2]));
            if (fabsf(d) <= pvs) {                  // near-surface band
              ++near;
              if (dist < minz) minz = dist;
              if (dist > maxz) maxz = dist;
              if (dist > R + 3.0f * pvs) ++outside_circ;
            }
          }
      printf("[%s] faces=%d inrad=%.3f minz=%.3f maxz=%.3f near=%d\n",
             solids[si].name, solids[si].faces, (double)inrad,
             (double)minz, (double)maxz, near);
      EXPECT(range_bad == 0, "platonic out of [-bg,bg]");
      EXPECT(neg > 0 && pos > 0, "platonic needs interior+exterior");
      EXPECT(near > 0, "platonic needs a near-surface band");
      EXPECT(outside_circ == 0, "near-surface voxel beyond circumradius");
      EXPECT(minz <= inrad + band && minz >= inrad - band, "min surface ~ inradius");
      EXPECT(maxz >= R - band, "surface reaches circumradius (vertices)");
      // Deep interior center clamps to -bg (inradius > bg here).
      int ci = (int)lroundf((ctr[0]-g.ox)/pvs - 0.5f);
      int cj = (int)lroundf((ctr[1]-g.oy)/pvs - 0.5f);
      int ck = (int)lroundf((ctr[2]-g.oz)/pvs - 0.5f);
      EXPECT(fabsf(at(&g, ci, cj, ck) + pbg) < 1e-5f, "platonic center == -bg");
      tvdb_dense_grid_free(&g);
    }
  }

  // ---- Segmentation: two separated spheres -> two components ----
  {
    tvdb_dense_grid g;
    int nx = 70, ny = 32, nz = 32;
    tvdb_dense_grid_init(&g, nx, ny, nz);
    g.voxel_size = 0.1f; g.ox = 0.0f; g.oy = 0.0f; g.oz = 0.0f;
    float ca[3] = { 1.5f, 1.6f, 1.6f }, cb[3] = { 5.5f, 1.6f, 1.6f }, r = 0.7f;
    int in_neg = 0;
    for (int k = 0; k < nz; ++k)
      for (int j = 0; j < ny; ++j)
        for (int i = 0; i < nx; ++i) {
          float x, y, z; wc(&g, i, j, k, &x, &y, &z);
          float da = sqrtf((x-ca[0])*(x-ca[0])+(y-ca[1])*(y-ca[1])+(z-ca[2])*(z-ca[2])) - r;
          float db = sqrtf((x-cb[0])*(x-cb[0])+(y-cb[1])*(y-cb[1])+(z-cb[2])*(z-cb[2])) - r;
          float d = da < db ? da : db;
          g.data[(size_t)(k*ny+j)*nx+i] = d;
          if (d < 0.0f) ++in_neg;
        }
    tvdb_dense_grid* segs = NULL; int nseg = 0;
    EXPECT(tvdb_sdf_segmentation(&g, 0.0f, 6, &segs, &nseg), "segmentation ok");
    EXPECT(nseg == 2, "two separated spheres -> 2 components");
    int tot_neg = 0;
    for (int c = 0; c < nseg; ++c) {
      int neg = 0; float xmin = 1e9f, xmax = -1e9f;
      for (int k = 0; k < nz; ++k)
        for (int j = 0; j < ny; ++j)
          for (int i = 0; i < nx; ++i)
            if (segs[c].data[(size_t)(k*ny+j)*nx+i] < 0.0f) {
              ++neg; float x = g.ox + (i+0.5f)*g.voxel_size;
              if (x < xmin) xmin = x; if (x > xmax) xmax = x;
            }
      tot_neg += neg;
      EXPECT(neg > 0, "each segment has interior");
      EXPECT(xmax - xmin < 2.0f, "each segment's interior is one localized blob");
    }
    EXPECT(tot_neg == in_neg, "segments partition the interior exactly");
    for (int c = 0; c < nseg; ++c) tvdb_dense_grid_free(&segs[c]);
    free(segs);
    tvdb_dense_grid_free(&g);
  }

  // ---- Enclosed regions: spherical shell cavity ----
  {
    tvdb_dense_grid g;
    int nx = 40, ny = 40, nz = 40;
    tvdb_dense_grid_init(&g, nx, ny, nz);
    g.voxel_size = 0.1f; g.ox = -2.0f; g.oy = -2.0f; g.oz = -2.0f;
    float R = 1.2f, ri = 0.7f;   // shell between ri and R, cavity for |p| < ri
    for (int k = 0; k < nz; ++k)
      for (int j = 0; j < ny; ++j)
        for (int i = 0; i < nx; ++i) {
          float x, y, z; wc(&g, i, j, k, &x, &y, &z);
          float rr = sqrtf(x*x + y*y + z*z);
          float d = (rr - R) > (ri - rr) ? (rr - R) : (ri - rr);  // shell SDF
          g.data[(size_t)(k*ny+j)*nx+i] = d;
        }
    tvdb_dense_grid mask;
    EXPECT(tvdb_sdf_extract_enclosed_regions(&g, 0.0f, 6, &mask), "enclosed ok");
    int marked = 0, bad = 0;
    for (int k = 0; k < nz; ++k)
      for (int j = 0; j < ny; ++j)
        for (int i = 0; i < nx; ++i) {
          float x, y, z; wc(&g, i, j, k, &x, &y, &z);
          float rr = sqrtf(x*x + y*y + z*z);
          float m = mask.data[(size_t)(k*ny+j)*nx+i];
          if (m != 0.0f && m != 1.0f) ++bad;
          if (m == 1.0f) {
            ++marked;
            if (rr > ri + 1e-4f) ++bad;        // marked must be inside the cavity
          } else {
            if (rr < ri - g.voxel_size) ++bad; // deep cavity must be marked
          }
        }
    EXPECT(bad == 0, "enclosed mask matches the cavity |p|<ri");
    EXPECT(marked > 0, "cavity should be found");
    tvdb_dense_grid_free(&g);
    tvdb_dense_grid_free(&mask);
  }

  // ---- Euler characteristic / genus ----
  {
    float c0[3] = { 0, 0, 0 };
    tvdb_dense_grid s;
    tvdb_level_set_sphere(1.0f, c0, 0.05f, 3.0f, &s);
    EXPECT(fabs(tvdb_level_set_euler_characteristic(&s, 0.0f) - 2.0) < 1e-9, "sphere euler=2");
    EXPECT(tvdb_level_set_genus(&s, 0.0f) == 0, "sphere genus=0");
    tvdb_dense_grid_free(&s);

    tvdb_dense_grid b; float he[3] = { 0.6f, 0.5f, 0.7f };
    tvdb_level_set_box(he, c0, 0.05f, 3.0f, &b);
    EXPECT(fabs(tvdb_level_set_euler_characteristic(&b, 0.0f) - 2.0) < 1e-9, "box euler=2");
    EXPECT(tvdb_level_set_genus(&b, 0.0f) == 0, "box genus=0");
    tvdb_dense_grid_free(&b);

    tvdb_dense_grid t;
    tvdb_level_set_torus(1.0f, 0.35f, c0, 0.05f, 3.0f, &t);
    EXPECT(fabs(tvdb_level_set_euler_characteristic(&t, 0.0f) - 0.0) < 1e-9, "torus euler=0");
    EXPECT(tvdb_level_set_genus(&t, 0.0f) == 1, "torus genus=1");
    tvdb_dense_grid_free(&t);

    // Two separated spheres: euler 4, genus 0.
    {
      tvdb_dense_grid g; int nx = 80, ny = 34, nz = 34;
      tvdb_dense_grid_init(&g, nx, ny, nz);
      g.voxel_size = 0.1f; g.ox = g.oy = g.oz = 0.0f;
      float a[3] = { 1.7f, 1.7f, 1.7f }, bb[3] = { 5.9f, 1.7f, 1.7f }, r = 0.8f;
      for (int k = 0; k < nz; ++k)
        for (int j = 0; j < ny; ++j)
          for (int i = 0; i < nx; ++i) {
            float x, y, z; wc(&g, i, j, k, &x, &y, &z);
            float da = sqrtf((x-a[0])*(x-a[0])+(y-a[1])*(y-a[1])+(z-a[2])*(z-a[2])) - r;
            float db = sqrtf((x-bb[0])*(x-bb[0])+(y-bb[1])*(y-bb[1])+(z-bb[2])*(z-bb[2])) - r;
            g.data[(size_t)(k*ny+j)*nx+i] = da < db ? da : db;
          }
      EXPECT(fabs(tvdb_level_set_euler_characteristic(&g, 0.0f) - 4.0) < 1e-9, "two spheres euler=4");
      EXPECT(tvdb_level_set_genus(&g, 0.0f) == 0, "two spheres genus=0");
      tvdb_dense_grid_free(&g);
    }

    // Two separated tori: euler 0, total genus 2.
    {
      tvdb_dense_grid g; int nx = 100, ny = 34, nz = 34;
      tvdb_dense_grid_init(&g, nx, ny, nz);
      g.voxel_size = 0.1f; g.ox = g.oy = g.oz = 0.0f;
      float ax = 1.7f, bx = 6.2f, cy = 1.7f, cz = 1.7f, R = 1.0f, r = 0.35f;
      for (int k = 0; k < nz; ++k)
        for (int j = 0; j < ny; ++j)
          for (int i = 0; i < nx; ++i) {
            float x, y, z; wc(&g, i, j, k, &x, &y, &z);
            float qa = sqrtf((x-ax)*(x-ax)+(z-cz)*(z-cz)) - R;
            float da = sqrtf(qa*qa + (y-cy)*(y-cy)) - r;
            float qb = sqrtf((x-bx)*(x-bx)+(z-cz)*(z-cz)) - R;
            float db = sqrtf(qb*qb + (y-cy)*(y-cy)) - r;
            g.data[(size_t)(k*ny+j)*nx+i] = da < db ? da : db;
          }
      EXPECT(fabs(tvdb_level_set_euler_characteristic(&g, 0.0f) - 0.0) < 1e-9, "two tori euler=0");
      EXPECT(tvdb_level_set_genus(&g, 0.0f) == 2, "two tori genus=2");
      tvdb_dense_grid_free(&g);
    }
  }

  // ---- Error paths ----
  {
    tvdb_dense_grid g;
    float c[3] = { 0,0,0 };
    EXPECT(!tvdb_level_set_sphere(-1.0f, c, vs, hw, &g), "negative radius rejected");
    EXPECT(!tvdb_level_set_sphere(1.0f, c, 0.0f, hw, &g), "zero voxel rejected");
    EXPECT(!tvdb_level_set_platonic(5, 1.0f, c, vs, hw, &g), "bad face_count rejected");
  }

  if (fails) { fprintf(stderr, "%d FAILURES\n", fails); return 1; }
  printf("All level-set tests passed.\n");
  return 0;
}
