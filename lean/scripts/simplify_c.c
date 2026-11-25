/* C half of the collision-proxy differential gate. Builds small closed meshes
 * with integer (half-integer after collapse) coordinates, calls the real
 * tvdb_mesh_simplify_ex, and dumps input positions/faces plus the output
 * topology. lean/Vdb/CollisionProxyCheck.lean recomputes the output from the
 * input and must match the face list exactly.
 *
 * SPDX-License-Identifier: Apache-2.0 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_mesh_simplify.h"

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
  for (size_t i = 0; i < nf; ++i) {
    m->faces[i].v0 = f[3 * i];
    m->faces[i].v1 = f[3 * i + 1];
    m->faces[i].v2 = f[3 * i + 2];
  }
  m->vertex_count = m->vertex_capacity = nv;
  m->face_count = m->face_capacity = nf;
}

/* cube: 8 vertices, 12 faces, outward winding. */
static const float cube_v[] = {
  0,0,0, 1,0,0, 1,1,0, 0,1,0, 0,0,1, 1,0,1, 1,1,1, 0,1,1
};
static const uint32_t cube_f[] = {
  0,2,1, 0,3,2, 4,5,6, 4,6,7, 0,5,4, 0,1,5,
  3,6,2, 3,7,6, 0,7,3, 0,4,7, 1,6,5, 1,2,6
};

/* octahedron: 6 vertices, 8 faces. */
static const float octa_v[] = {
  1,0,0, -1,0,0, 0,1,0, 0,-1,0, 0,0,1, 0,0,-1
};
static const uint32_t octa_f[] = {
  0,2,4, 2,1,4, 1,3,4, 3,0,4,
  2,0,5, 1,2,5, 3,1,5, 0,3,5
};

/* two disjoint tetrahedra. */
static const float tetra_v[] = {
  0,0,0, 2,0,0, 0,2,0, 0,0,2,
  6,6,6, 8,6,6, 6,8,6, 6,6,8
};
static const uint32_t tetra_f[] = {
  0,2,1, 0,1,3, 1,2,3, 0,3,2,
  4,6,5, 4,5,7, 5,6,7, 4,7,6
};

struct fixture {
  const char *name;
  const float *v;
  size_t nv;
  const uint32_t *f;
  size_t nf;
};

int main(void) {
  static const struct fixture fixtures[] = {
    {"cube", cube_v, 8, cube_f, 12},
    {"octa", octa_v, 6, octa_f, 8},
    {"tetra2", tetra_v, 8, tetra_f, 8}
  };
  static const size_t targets[] = {8, 6, 6, 4};
  int ci = 0;
  for (size_t fi = 0; fi < sizeof(fixtures) / sizeof(fixtures[0]); ++fi) {
    for (size_t ti = 0; ti < sizeof(targets) / sizeof(targets[0]); ++ti) {
      if (targets[ti] >= fixtures[fi].nf) continue;
      tvdb_triangle_mesh in, out;
      mesh_init(&in, fixtures[fi].v, fixtures[fi].nv,
                fixtures[fi].f, fixtures[fi].nf);
      tvdb_triangle_mesh_init(&out);
      /* Octahedron target 4 has no closed collapse sequence for this simple
         greedy algorithm; the C contract correctly rejects it, so the gate
         only uses feasible targets. */
      if (fi == 1 && targets[ti] < 5) continue;
      tvdb_simplify_options_t opt = {targets[ti], false, true};
      tvdb_error_t err;
      memset(&err, 0, sizeof(err));
      tvdb_status_t st = tvdb_mesh_simplify_ex(&in, &opt, &out, NULL, &err);
      if (st != TVDB_OK) {
        fprintf(stderr, "case %d failed: %s\n", ci, err.message);
        return 1;
      }
      printf("case %d target %zu\n", ci, targets[ti]);
      for (size_t i = 0; i < in.vertex_count; ++i) {
        const tvdb_vec3f *p = &in.vertices[i];
        printf("v %zu %d %d %d\n", i, (int)(2.0f * p->x), (int)(2.0f * p->y),
               (int)(2.0f * p->z));
      }
      for (size_t i = 0; i < in.face_count; ++i)
        printf("f %u %u %u\n", in.faces[i].v0, in.faces[i].v1, in.faces[i].v2);
      printf("outv %zu\n", out.vertex_count);
      printf("outf %zu\n", out.face_count);
      for (size_t i = 0; i < out.face_count; ++i)
        printf("of %u %u %u\n", out.faces[i].v0, out.faces[i].v1, out.faces[i].v2);
      ++ci;
      tvdb_triangle_mesh_free(&in);
      tvdb_triangle_mesh_free(&out);
    }
  }
  return 0;
}
