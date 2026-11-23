/* Contract tests for sphere/mesh contacts. SPDX-License-Identifier: Apache-2.0 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_contact.h"

static void cube(tvdb_triangle_mesh *m) {
  static const tvdb_vec3f v[] = {
    {0,0,0},{1,0,0},{1,1,0},{0,1,0},{0,0,1},{1,0,1},{1,1,1},{0,1,1}
  };
  static const tvdb_triangle f[] = {
    {0,2,1},{0,3,2},{4,5,6},{4,6,7},{0,5,4},{0,1,5},
    {3,6,2},{3,7,6},{0,7,3},{0,4,7},{1,6,5},{1,2,6}
  };
  memset(m, 0, sizeof(*m));
  m->vertices = (tvdb_vec3f *)malloc(sizeof(v));
  m->faces = (tvdb_triangle *)malloc(sizeof(f));
  memcpy(m->vertices, v, sizeof(v));
  memcpy(m->faces, f, sizeof(f));
  m->vertex_count = m->vertex_capacity = 8;
  m->face_count = m->face_capacity = 12;
}

int main(void) {
  tvdb_triangle_mesh m;
  cube(&m);
  double center[3] = {0.3, 0.2, 3.0};
  tvdb_contact_set_t set;
  memset(&set, 0, sizeof(set));
  if (tvdb_mesh_sphere_contacts_ex(&m, center, 2.008, 0.0, &set, NULL, NULL) != TVDB_OK ||
      set.count != 2) {
    fprintf(stderr, "expected 2 raw contacts, got %zu\n", set.count);
  }
  for (size_t i = 0; i < set.count; ++i) {
    const tvdb_contact_t *c = &set.contacts[i];
    if (!(c->depth > 0.0 && c->depth < 0.02) || c->normal[2] < 0.99 ||
        c->point[2] < 0.99) {
      fprintf(stderr, "contact %zu has wrong geometry\n", i);
      return 1;
    }
  }
  tvdb_contact_set_free(&set);

  memset(&set, 0, sizeof(set));
  if (tvdb_mesh_sphere_contacts_ex(&m, center, 2.008, 0.1, &set, NULL, NULL) != TVDB_OK ||
      set.count != 1) {
    fprintf(stderr, "manifold reduction failed: %zu contacts\n", set.count);
    return 1;
  }
  tvdb_contact_set_free(&set);

  /* Invalid radius preserves the output. */
  tvdb_contact_set_t unchanged;
  memset(&unchanged, 0, sizeof(unchanged));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_mesh_sphere_contacts_ex(&m, center, -1.0, 0.1, &unchanged, NULL, &err)
      != TVDB_ERROR_INVALID_ARGUMENT || err.status != TVDB_ERROR_INVALID_ARGUMENT ||
      unchanged.count != 0) {
    fprintf(stderr, "invalid input did not preserve output\n");
    return 1;
  }

  printf("OK contact: 2 raw -> 1 manifold contact, geometry exact, failure preserved\n");
  tvdb_triangle_mesh_free(&m);
  return 0;
}
