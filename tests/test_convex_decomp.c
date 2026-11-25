/* Contract tests for convex part decomposition. SPDX-License-Identifier: Apache-2.0 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_convex_decomp.h"

static void mesh_init(tvdb_triangle_mesh *m, const float *v, size_t nv,
                      const uint32_t *f, size_t nf) {
  memset(m, 0, sizeof(*m));
  m->vertices = (tvdb_vec3f *)malloc(nv * sizeof(tvdb_vec3f));
  m->faces = (tvdb_triangle *)malloc(nf * sizeof(tvdb_triangle));
  for (size_t i = 0; i < nv; ++i) {
    m->vertices[i].x = v[3 * i];
    m->vertices[i].y = v[3 * i + 1];
    m->vertices[i].z = v[3 * i + 2];
  }
  memcpy(m->faces, f, nf * sizeof(tvdb_triangle));
  m->vertex_count = m->vertex_capacity = nv;
  m->face_count = m->face_capacity = nf;
}

static int box_contains(const tvdb_convex_part_t *p, const tvdb_vec3f *v) {
  double q[3] = {v->x, v->y, v->z};
  for (int d = 0; d < 3; ++d)
    if (q[d] < p->lo[d] || q[d] > p->hi[d]) return 0;
  return 1;
}

int main(void) {
  static const float v[] = {
    0,0,0, 2,0,0, 0,2,0, 0,0,2,
    10,10,10, 12,10,10, 10,12,10, 10,10,12
  };
  static const uint32_t f[] = {
    0,2,1, 0,1,3, 1,2,3, 0,3,2,
    4,6,5, 4,5,7, 5,6,7, 4,7,6
  };
  tvdb_triangle_mesh m;
  mesh_init(&m, v, 8, f, 8);
  tvdb_convex_decomp_t d;
  memset(&d, 0, sizeof(d));
  if (tvdb_mesh_convex_decompose_ex(&m, &d, NULL, NULL) != TVDB_OK ||
      d.part_count != 2 || d.label_count != 8) {
    fprintf(stderr, "expected 2 convex parts, got %zu\n", d.part_count);
    return 1;
  }
  for (size_t i = 0; i < 8; ++i)
    if (!box_contains(&d.parts[d.labels[i]], &m.vertices[i])) {
      fprintf(stderr, "box %u does not contain vertex %zu\n", d.labels[i], i);
      return 1;
    }
  for (size_t p = 0; p < d.part_count; ++p)
    if (d.parts[p].face_count != 4) {
      fprintf(stderr, "part %zu has %u faces\n", p, d.parts[p].face_count);
      return 1;
    }
  tvdb_convex_decomp_free(&d);

  /* Invalid face index fails and leaves the output untouched. */
  tvdb_triangle_mesh bad = m;
  bad.faces = (tvdb_triangle *)malloc(sizeof(tvdb_triangle));
  bad.faces[0] = (tvdb_triangle){0, 1, 99};
  bad.face_count = bad.face_capacity = 1;
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  tvdb_convex_decomp_t unchanged;
  memset(&unchanged, 0, sizeof(unchanged));
  if (tvdb_mesh_convex_decompose_ex(&bad, &unchanged, NULL, &err) != TVDB_ERROR_INVALID_DATA ||
      err.status != TVDB_ERROR_INVALID_DATA || unchanged.part_count != 0) {
    fprintf(stderr, "invalid input did not fail cleanly\n");
    return 1;
  }
  free(bad.faces);

  printf("OK convex_decomp: 2 parts, all vertices covered, failure preserved\n");
  tvdb_triangle_mesh_free(&m);
  return 0;
}
