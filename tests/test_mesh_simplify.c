/* Contract tests for the collision-proxy simplifier.
 * SPDX-License-Identifier: Apache-2.0 */
#include <math.h>
#include <stdio.h>
#include <string.h>

#include "tinyvdb_mesh_simplify.h"

static void cube(tvdb_triangle_mesh *m) {
  static const tvdb_vec3f v[8] = {
    {0,0,0},{1,0,0},{1,1,0},{0,1,0},
    {0,0,1},{1,0,1},{1,1,1},{0,1,1}
  };
  static const tvdb_triangle f[12] = {
    {0,2,1},{0,3,2},  /* bottom  z=0, outward -z */
    {4,5,6},{4,6,7},  /* top     z=1, outward +z */
    {0,5,4},{0,1,5},  /* front   y=0, outward -y */
    {3,6,2},{3,7,6},  /* back    y=1, outward +y */
    {0,7,3},{0,4,7},  /* left    x=0, outward -x */
    {1,6,5},{1,2,6}   /* right   x=1, outward +x */
  };
  memset(m, 0, sizeof(*m));
  m->vertices = (tvdb_vec3f *)malloc(sizeof(v));
  m->faces = (tvdb_triangle *)malloc(sizeof(f));
  memcpy(m->vertices, v, sizeof(v));
  memcpy(m->faces, f, sizeof(f));
  m->vertex_count = m->vertex_capacity = 8;
  m->face_count = m->face_capacity = 12;
}

static int has_edge(const tvdb_triangle_mesh *m, uint32_t a, uint32_t b) {
  for (size_t i = 0; i < m->face_count; ++i) {
    const tvdb_triangle *t = &m->faces[i];
    if ((t->v0 == a && t->v1 == b) || (t->v1 == a && t->v2 == b) ||
        (t->v2 == a && t->v0 == b)) return 1;
  }
  return 0;
}

static int closed(const tvdb_triangle_mesh *m) {
  for (size_t i = 0; i < m->face_count; ++i) {
    const tvdb_triangle *t = &m->faces[i];
    uint32_t a[3] = {t->v0, t->v1, t->v2};
    if (a[0] == a[1] || a[1] == a[2] || a[0] == a[2]) return 0;
    for (int e = 0; e < 3; ++e)
      if (!has_edge(m, a[(e + 1) % 3], a[e])) return 0;
  }
  return 1;
}

static int same_topology(const tvdb_triangle_mesh *a, const tvdb_triangle_mesh *b) {
  if (a->vertex_count != b->vertex_count || a->face_count != b->face_count) return 0;
  for (size_t i = 0; i < a->face_count; ++i)
    if (memcmp(&a->faces[i], &b->faces[i], sizeof(tvdb_triangle)) != 0) return 0;
  for (size_t i = 0; i < a->vertex_count; ++i) {
    const tvdb_vec3f *p = &a->vertices[i], *q = &b->vertices[i];
    if (fabsf(p->x - q->x) > 1e-6f || fabsf(p->y - q->y) > 1e-6f ||
        fabsf(p->z - q->z) > 1e-6f) return 0;
  }
  return 1;
}

int main(void) {
  tvdb_triangle_mesh in, out, out2;
  cube(&in);
  if (!closed(&in)) { fprintf(stderr, "fixture is not closed\n"); return 1; }

  tvdb_triangle_mesh_init(&out);
  tvdb_simplify_options_t opt = {8, true, true};
  if (tvdb_mesh_simplify_ex(&in, &opt, &out, NULL, NULL) != TVDB_OK) {
    fprintf(stderr, "simplify to 8 failed\n"); return 1;
  }
  if (out.face_count == 0 || out.face_count > 8 || !closed(&out)) {
    fprintf(stderr, "simplified mesh invalid: %zu faces\n", out.face_count); return 1;
  }

  /* No-op path: target at least the input face count copies the mesh. */
  tvdb_triangle_mesh_init(&out2);
  tvdb_simplify_options_t copyopt = {12, true, true};
  if (tvdb_mesh_simplify_ex(&in, &copyopt, &out2, NULL, NULL) != TVDB_OK ||
      out2.face_count != 12 || !closed(&out2)) {
    fprintf(stderr, "copy path failed\n"); return 1;
  }

  /* Invalid face index: failure preserves the output. */
  tvdb_triangle_mesh bad = in;
  bad.faces = (tvdb_triangle *)malloc(sizeof(tvdb_triangle));
  bad.faces[0] = (tvdb_triangle){0, 1, 99};
  bad.face_count = bad.face_capacity = 1;
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  size_t before = out.face_count;
  if (tvdb_mesh_simplify_ex(&bad, &opt, &out, NULL, &err) == TVDB_OK ||
      err.status != TVDB_ERROR_INVALID_DATA || out.face_count != before) {
    fprintf(stderr, "invalid input did not preserve output\n"); return 1;
  }
  free(bad.faces);

  /* Aliasing rejection. */
  if (tvdb_mesh_simplify_ex(&in, &opt, &in, NULL, NULL) != TVDB_ERROR_INVALID_ARGUMENT) {
    fprintf(stderr, "alias not rejected\n"); return 1;
  }

  /* Determinism: two independent runs give the same topology and positions. */
  tvdb_triangle_mesh a, b;
  tvdb_triangle_mesh_init(&a);
  tvdb_triangle_mesh_init(&b);
  if (tvdb_mesh_simplify_ex(&in, &opt, &a, NULL, NULL) != TVDB_OK ||
      tvdb_mesh_simplify_ex(&in, &opt, &b, NULL, NULL) != TVDB_OK ||
      !same_topology(&a, &b)) {
    fprintf(stderr, "non-deterministic output\n"); return 1;
  }

  printf("OK mesh_simplify: %zu -> %zu faces, closed, deterministic\n",
         in.face_count, out.face_count);
  tvdb_triangle_mesh_free(&in);
  tvdb_triangle_mesh_free(&out);
  tvdb_triangle_mesh_free(&out2);
  tvdb_triangle_mesh_free(&a);
  tvdb_triangle_mesh_free(&b);
  return 0;
}
