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

typedef struct {
  double eps;   /* coplanarity tolerance; 0 selects 1e-9 */
} tvdb_convex_hull_options_t;

/* Convex hull of a small point set (3 doubles per point) by the deterministic
   all-triples supporting-plane test. Only strictly supporting triples become
   faces; coplanar point sets are rejected with TVDB_ERROR_INVALID_DATA. The
   output mesh owns its buffers and follows the usual _ex contract. */
tvdb_status_t tvdb_points_convex_hull_ex(const double *points, size_t count,
    const tvdb_convex_hull_options_t *options, tvdb_triangle_mesh *out,
    tvdb_arena_allocator_t *arena, tvdb_error_t *err);

bool tvdb_points_convex_hull(const double *points, size_t count,
    tvdb_triangle_mesh *out, tvdb_arena_allocator_t *arena);

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
