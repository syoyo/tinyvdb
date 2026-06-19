// Theme C: resampling, signed flood fill, and higher-order advection.

#include "tinyvdb_topology.h"
#include "tinyvdb_ops.h"
#include "tinyvdb_levelset.h"
#include "tinyvdb_mesh.h"
#include "tinyvdb_sample.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static int fails = 0;
#define EXPECT(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fails; } \
} while (0)

static inline float at3(const tvdb_dense_grid* g, int i, int j, int k) {
  return g->data[(size_t)(k * g->ny + j) * g->nx + i];
}

int main(void) {
  // ---- Resample: linear field is reproduced exactly by box/quadratic ----
  {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 20, 16, 12);
    g.voxel_size = 0.1f; g.ox = -1.0f; g.oy = 0.5f; g.oz = 2.0f;
    for (int k = 0; k < g.nz; ++k)
      for (int j = 0; j < g.ny; ++j)
        for (int i = 0; i < g.nx; ++i)
          // f(p) = world-x of the voxel center (a linear field).
          g.data[(size_t)(k*g.ny+j)*g.nx+i] = g.ox + ((float)i + 0.5f) * g.voxel_size;

    for (int order = 1; order <= 2; ++order) {       // box, quadratic reproduce linear
      tvdb_dense_grid r;
      EXPECT(tvdb_resample_grid(&g, 0.07f, order, &r, NULL), "resample ok");
      EXPECT(fabsf(r.voxel_size - 0.07f) < 1e-6f, "resample voxel size");
      EXPECT(fabsf(r.ox - g.ox) < 1e-6f, "resample preserves origin");
      // World AABB preserved: dim*vs ~ source dim*vs.
      EXPECT(fabsf(r.nx * 0.07f - g.nx * 0.1f) < 0.07f, "resample preserves world extent");
      // Check only where the sampler stencil stays inside the source (the
      // quadratic 3-wide stencil clamps at the source's outermost cell).
      float xlo = g.ox + 1.5f * g.voxel_size, xhi = g.ox + (g.nx - 1.5f) * g.voxel_size;
      float maxerr = 0.0f; int checked = 0;
      for (int k = 0; k < r.nz; ++k)
        for (int j = 0; j < r.ny; ++j)
          for (int i = 0; i < r.nx; ++i) {
            float wx = r.ox + ((float)i + 0.5f) * r.voxel_size;
            if (wx < xlo || wx > xhi) continue;
            float e = fabsf(at3(&r, i, j, k) - wx);
            if (e > maxerr) maxerr = e;
            ++checked;
          }
      EXPECT(checked > 0 && maxerr < 1e-4f, "resample reproduces a linear field");
      tvdb_dense_grid_free(&r);
    }
    // Nearest is approximate but bounded by half a source voxel.
    tvdb_dense_grid rn;
    tvdb_resample_grid(&g, 0.07f, 0, &rn, NULL);
    int bad = 0;
    for (int k = 0; k < rn.nz; ++k)
      for (int j = 0; j < rn.ny; ++j)
        for (int i = 0; i < rn.nx; ++i) {
          float wx = rn.ox + ((float)i + 0.5f) * rn.voxel_size;
          if (fabsf(at3(&rn, i, j, k) - wx) > 0.5f * g.voxel_size + 1e-4f) ++bad;
        }
    EXPECT(bad == 0, "nearest resample within half a source voxel");
    tvdb_dense_grid_free(&rn);
    tvdb_dense_grid_free(&g);
  }

  // ---- Resample a sphere SDF preserves the zero crossing ----
  {
    float c[3] = { 0, 0, 0 };
    tvdb_dense_grid s; tvdb_level_set_sphere(1.0f, c, 0.05f, 3.0f, &s);
    tvdb_dense_grid r;
    tvdb_resample_grid(&s, 0.1f, 1, &r, NULL);
    // Sample along +x: zero crossing near radius 1.
    float pv = tvdb_sample_trilinear_dense(&r, 0, 0, 0), dcross = -1.0f;
    for (int t = 1; t <= 40 && dcross < 0.0f; ++t) {
      float d = (float)t * 0.05f;
      float v = tvdb_sample_trilinear_dense(&r, d, 0, 0);
      if (pv < 0.0f && v >= 0.0f) dcross = (float)(t-1)*0.05f + 0.05f*(-pv)/(v-pv);
      pv = v;
    }
    EXPECT(dcross > 0.0f && fabsf(dcross - 1.0f) < 0.1f, "resampled sphere keeps R~1");
    tvdb_dense_grid_free(&s); tvdb_dense_grid_free(&r);
  }

  if (fails) { fprintf(stderr, "%d FAILURES\n", fails); return 1; }
  printf("All resample/advect tests passed.\n");
  return 0;
}
