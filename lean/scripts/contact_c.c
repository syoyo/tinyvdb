/* C half of the contact differential gate. SPDX-License-Identifier: Apache-2.0 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_contact.h"

static const tvdb_vec3f cv[] = {
  {0,0,0},{1,0,0},{1,1,0},{0,1,0},{0,0,1},{1,0,1},{1,1,1},{0,1,1}
};
static const tvdb_triangle cf[] = {
  {0,2,1},{0,3,2},{4,5,6},{4,6,7},{0,5,4},{0,1,5},
  {3,6,2},{3,7,6},{0,7,3},{0,4,7},{1,6,5},{1,2,6}
};

struct query { double c[3]; double r; double merge; };

int main(void) {
  static const struct query qs[] = {
    {{0.3, 0.2, 3.0}, 2.008, 0.1},
    {{0.3, 0.2, 3.0}, 2.008, 0.0},
    {{0.5, 0.5, -2.0}, 2.5, 0.1}
  };
  for (size_t qi = 0; qi < sizeof(qs)/sizeof(qs[0]); ++qi) {
    tvdb_triangle_mesh m;
    memset(&m, 0, sizeof(m));
    m.vertices = (tvdb_vec3f *)malloc(sizeof(cv));
    m.faces = (tvdb_triangle *)malloc(sizeof(cf));
    memcpy(m.vertices, cv, sizeof(cv));
    memcpy(m.faces, cf, sizeof(cf));
    m.vertex_count = m.vertex_capacity = 8;
    m.face_count = m.face_capacity = 12;

    tvdb_contact_set_t set;
    memset(&set, 0, sizeof(set));
    if (tvdb_mesh_sphere_contacts_ex(&m, qs[qi].c, qs[qi].r, qs[qi].merge,
                                     &set, NULL, NULL) != TVDB_OK) return 1;
    printf("case %zu\n", qi);
    for (size_t i = 0; i < 8; ++i)
      printf("v %zu %d %d %d\n", i, (int)(2*m.vertices[i].x),
             (int)(2*m.vertices[i].y), (int)(2*m.vertices[i].z));
    for (size_t i = 0; i < 12; ++i)
      printf("f %u %u %u\n", m.faces[i].v0, m.faces[i].v1, m.faces[i].v2);
    printf("query %d %d %d %d %d\n",
           (int)(1000*qs[qi].c[0]), (int)(1000*qs[qi].c[1]), (int)(1000*qs[qi].c[2]),
           (int)(1000*qs[qi].r), (int)(1000*qs[qi].merge));
    printf("out %zu\n", set.count);
    for (size_t i = 0; i < set.count; ++i)
      printf("contact %u %.9f %.9f %.9f %.9f\n", set.contacts[i].face,
             set.contacts[i].point[0], set.contacts[i].point[1],
             set.contacts[i].point[2], set.contacts[i].depth);
    tvdb_contact_set_free(&set);
    tvdb_triangle_mesh_free(&m);
  }
  return 0;
}
