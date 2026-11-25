/* C half of the convex-part differential gate. SPDX-License-Identifier: Apache-2.0 */
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

static const float cube_v[] = {
  0,0,0, 1,0,0, 1,1,0, 0,1,0, 0,0,1, 1,0,1, 1,1,1, 0,1,1
};
static const uint32_t cube_f[] = {
  0,2,1, 0,3,2, 4,5,6, 4,6,7, 0,5,4, 0,1,5,
  3,6,2, 3,7,6, 0,7,3, 0,4,7, 1,6,5, 1,2,6
};
static const float tetra_v[] = {
  0,0,0, 2,0,0, 0,2,0, 0,0,2,
  10,10,10, 12,10,10, 10,12,10, 10,10,12
};
static const uint32_t tetra_f[] = {
  0,2,1, 0,1,3, 1,2,3, 0,3,2,
  4,6,5, 4,5,7, 5,6,7, 4,7,6
};

int main(void) {
  struct { const char *name; const float *v; size_t nv; const uint32_t *f; size_t nf; } fx[] = {
    {"cube", cube_v, 8, cube_f, 12},
    {"tetra2", tetra_v, 8, tetra_f, 8}
  };
  int ci = 0;
  for (size_t i = 0; i < sizeof(fx) / sizeof(fx[0]); ++i) {
    tvdb_triangle_mesh m;
    mesh_init(&m, fx[i].v, fx[i].nv, fx[i].f, fx[i].nf);
    tvdb_convex_decomp_t d;
    memset(&d, 0, sizeof(d));
    if (tvdb_mesh_convex_decompose_ex(&m, &d, NULL, NULL) != TVDB_OK) return 1;
    printf("case %d\n", ci++);
    for (size_t v = 0; v < m.vertex_count; ++v)
      printf("v %zu %d %d %d\n", v,
             (int)(2.0f * m.vertices[v].x), (int)(2.0f * m.vertices[v].y),
             (int)(2.0f * m.vertices[v].z));
    for (size_t f = 0; f < m.face_count; ++f)
      printf("f %u %u %u\n", m.faces[f].v0, m.faces[f].v1, m.faces[f].v2);
    printf("parts %zu\n", d.part_count);
    for (size_t p = 0; p < d.part_count; ++p) {
      const tvdb_convex_part_t *q = &d.parts[p];
      printf("part %d %d %d %d %d %d %d\n",
             (int)(2.0 * q->lo[0]), (int)(2.0 * q->lo[1]), (int)(2.0 * q->lo[2]),
             (int)(2.0 * q->hi[0]), (int)(2.0 * q->hi[1]), (int)(2.0 * q->hi[2]),
             (int)q->first_face);
    }
    for (size_t v = 0; v < d.label_count; ++v)
      printf("label %zu %u\n", v, d.labels[v]);
    tvdb_convex_decomp_free(&d);
    tvdb_triangle_mesh_free(&m);
  }
  return 0;
}
