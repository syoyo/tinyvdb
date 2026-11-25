/* C half of the convex-hull gate. SPDX-License-Identifier: Apache-2.0 */
#include <stdio.h>
#include <stdlib.h>

#include "tinyvdb_convex_decomp.h"

int main(void) {
  static const double tetra[] = {0,0,0, 2,0,0, 0,2,0, 0,0,2};
  static const double octa[] = {1,0,0, -1,0,0, 0,1,0, 0,-1,0, 0,0,1, 0,0,-1};
  static const double cloud[] = {0,0,0, 3,0,0, 0,4,0, 0,0,5, 2,1,3, -1,2,2, 1,-2,2};
  struct { const double *p; size_t n; } cases[] = {
    {tetra, 4}, {octa, 6}, {cloud, 7}
  };
  for (size_t ci = 0; ci < sizeof(cases)/sizeof(cases[0]); ++ci) {
    tvdb_triangle_mesh m;
    tvdb_triangle_mesh_init(&m);
    tvdb_convex_hull_options_t opt = {0.0};
    tvdb_error_t err;
    if (tvdb_points_convex_hull_ex(cases[ci].p, cases[ci].n, &opt, &m, NULL, &err) != TVDB_OK) {
      fprintf(stderr, "case %zu failed: %s\n", ci, err.message);
      return 1;
    }
    printf("case %zu\n", ci);
    for (size_t i = 0; i < cases[ci].n; ++i)
      printf("p %zu %d %d %d\n", i,
             (int)(1000*cases[ci].p[3*i]), (int)(1000*cases[ci].p[3*i+1]),
             (int)(1000*cases[ci].p[3*i+2]));
    printf("out %zu\n", m.face_count);
    for (size_t i = 0; i < m.face_count; ++i)
      printf("face %u %u %u\n", m.faces[i].v0, m.faces[i].v1, m.faces[i].v2);
    tvdb_triangle_mesh_free(&m);
  }
  return 0;
}
