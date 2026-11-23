#pragma once
/* Sphere-vs-triangle-mesh contact generation with manifold reduction.
 *
 * For every triangle whose closest point to a sphere centre lies within the
 * radius, a contact is emitted with the closest point as position, the unit
 * direction toward the sphere centre as normal, and depth = radius − distance.
 * Contacts are sorted by decreasing depth (face index breaks ties) and reduced
 * greedily: a contact is kept only if it is farther than `merge_dist` from
 * every already-kept contact point. The reduction is deterministic and does
 * not depend on any worker pool.
 */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "tinyvdb_io.h"
#include "tinyvdb_mesh.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  double point[3];
  double normal[3];
  double depth;
  uint32_t face;
} tvdb_contact_t;

typedef struct {
  tvdb_contact_t *contacts;
  size_t count;
} tvdb_contact_set_t;

void tvdb_contact_set_free(tvdb_contact_set_t *set);

tvdb_status_t tvdb_mesh_sphere_contacts_ex(const tvdb_triangle_mesh *mesh,
    const double center[3], double radius, double merge_dist,
    tvdb_contact_set_t *out, tvdb_arena_allocator_t *arena, tvdb_error_t *err);

bool tvdb_mesh_sphere_contacts(const tvdb_triangle_mesh *mesh,
    const double center[3], double radius, double merge_dist,
    tvdb_contact_set_t *out, tvdb_arena_allocator_t *arena);

#ifdef __cplusplus
}
#endif
