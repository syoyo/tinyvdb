#pragma once
/* Convex part decomposition of a triangle mesh for physics collision proxies.
 *
 * Faces are grouped by shared-vertex connectivity (union-find over the mesh's
 * vertices, with each face unioning its three corners). Each connected part
 * gets the axis-aligned box of its vertices: a convex, deterministic proxy.
 * Parts are ordered by the lowest original vertex index in the component, so
 * the result is independent of any worker pool.
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
  double lo[3];
  double hi[3];
  uint32_t first_face;   /* first face index in the source mesh */
  uint32_t face_count;
} tvdb_convex_part_t;

typedef struct {
  tvdb_convex_part_t *parts;
  size_t part_count;
  uint32_t *labels;      /* one part index per source vertex */
  size_t label_count;
} tvdb_convex_decomp_t;

void tvdb_convex_decomp_free(tvdb_convex_decomp_t *decomp);

tvdb_status_t tvdb_mesh_convex_decompose_ex(const tvdb_triangle_mesh *mesh,
                                             tvdb_convex_decomp_t *out,
                                             tvdb_arena_allocator_t *arena,
                                             tvdb_error_t *err);

bool tvdb_mesh_convex_decompose(const tvdb_triangle_mesh *mesh,
                                 tvdb_convex_decomp_t *out,
                                 tvdb_arena_allocator_t *arena);

#ifdef __cplusplus
}
#endif
