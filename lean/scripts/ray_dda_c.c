/* C half of the ray-DDA differential gate. SPDX-License-Identifier: Apache-2.0 */
#include <stdio.h>
#include <stdlib.h>

#include "tinyvdb_ray.h"

struct ray_case {
  float o[3], d[3], tmin, tmax;
};

int main(void) {
  static const struct ray_case cases[] = {
    {{0.25f, 0.25f, -0.5f}, {1.0f, 0.5f, 0.25f}, 0.0f, 20.0f},
    {{-0.5f, 3.0f, 0.25f}, {0.5f, -0.25f, 1.0f}, 0.0f, 20.0f},
    {{0.5f, 0.5f, 0.5f}, {1.0f, 0.0f, 0.0f}, 0.0f, 20.0f},
    {{5.5f, 5.5f, 5.5f}, {-1.0f, -0.5f, -0.25f}, 0.0f, 20.0f}
  };
  tvdb_dense_grid g;
  tvdb_dense_grid_init(&g, 6, 6, 6);
  g.voxel_size = 1.0f; g.ox = g.oy = g.oz = 0.0f;
  for (size_t ci = 0; ci < sizeof(cases)/sizeof(cases[0]); ++ci) {
    tvdb_ray r;
    r.origin.x = cases[ci].o[0]; r.origin.y = cases[ci].o[1]; r.origin.z = cases[ci].o[2];
    r.dir.x = cases[ci].d[0]; r.dir.y = cases[ci].d[1]; r.dir.z = cases[ci].d[2];
    r.tmin = cases[ci].tmin; r.tmax = cases[ci].tmax;
    tvdb_vec3i voxels[64];
    size_t n = tvdb_voxels_along_ray_dense(&g, &r, voxels, 64);
    printf("case %zu\n", ci);
    printf("ray %d %d %d %d %d %d %d %d\n",
           (int)(1000*r.origin.x), (int)(1000*r.origin.y), (int)(1000*r.origin.z),
           (int)(1000*r.dir.x), (int)(1000*r.dir.y), (int)(1000*r.dir.z),
           (int)(1000*r.tmin), (int)(1000*r.tmax));
    printf("out %zu\n", n);
    for (size_t i = 0; i < n; ++i)
      printf("voxel %d %d %d\n", voxels[i].x, voxels[i].y, voxels[i].z);
  }
  tvdb_dense_grid_free(&g);
  return 0;
}
