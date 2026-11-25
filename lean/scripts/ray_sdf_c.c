/* C half of the SDF ray-crossing gate. SPDX-License-Identifier: Apache-2.0 */
#include <stdio.h>
#include <stdlib.h>

#include "tinyvdb_ray.h"

int main(void) {
  tvdb_dense_grid g;
  tvdb_dense_grid_init(&g, 8, 8, 8);
  g.voxel_size = 1.0f; g.ox = g.oy = g.oz = 0.0f;
  for (int k = 0; k < 8; ++k)
    for (int j = 0; j < 8; ++j)
      for (int i = 0; i < 8; ++i)
        g.data[(k*8 + j)*8 + i] = (i >= 2 && i <= 5) ? -1.0f : 1.0f;

  struct { float tmin, tmax; int steps; } cases[] = {
    {-0.5f, 7.5f, 17}, {-0.5f, 7.5f, 9}, {0.0f, 7.0f, 15}
  };
  for (size_t ci = 0; ci < sizeof(cases)/sizeof(cases[0]); ++ci) {
    tvdb_ray r;
    r.origin.x = cases[ci].tmin; r.origin.y = 3.5f; r.origin.z = 3.5f;
    r.dir.x = 1.0f; r.dir.y = 0.0f; r.dir.z = 0.0f;
    r.tmin = cases[ci].tmin; r.tmax = cases[ci].tmax;
    float pairs[32];
    size_t n = tvdb_segments_along_ray(&g, &r, 0.0f, (size_t)cases[ci].steps,
                                       pairs, 32);
    printf("case %zu\n", ci);
    printf("ray %d %d %d\n", (int)(1000*r.tmin), (int)(1000*r.tmax), cases[ci].steps);
    printf("out %zu\n", n);
    for (size_t i = 0; i < n; ++i)
      printf("pair %.9f %.9f\n", pairs[2*i], pairs[2*i+1]);
  }
  tvdb_dense_grid_free(&g);
  return 0;
}
