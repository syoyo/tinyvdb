#pragma once
/* Collision-proxy simplification: deterministic quadric-error-ranked edge
 * collapse on a triangle mesh. The algorithm is intentionally simple and
 * serial so its index-space output is reproducible by the Lean differential
 * twin (`lean/Vdb/CollisionProxyCheck.lean`):
 *
 *   1. accumulate one plane quadric per incident triangle at each vertex;
 *   2. rank every undirected edge by the accumulated quadric evaluated at the
 *      edge midpoint (QEM cost; the collapse target is the midpoint, not the
 *      full QEM optimum -- documented deviation);
 *   3. skip edges whose endpoints are on the boundary when requested, and
 *      skip edges that fail the link test (the two endpoints must share
 *      exactly the two opposite vertices of the incident faces);
 *   4. apply candidates in sorted (cost, i, j) order, retargeting the second
 *      endpoint and dropping faces that become degenerate.
 *
 * Success replaces `out` (freeing old heap storage; with an arena, old output
 * storage is retained until the caller resets the arena). Failure preserves
 * `out` and restores the arena offset. `out` must be initialized and must not
 * overlap the input or itself.
 */
#include <stdbool.h>
#include <stddef.h>

#include "tinyvdb_io.h"
#include "tinyvdb_mesh.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  size_t target_faces;     /* stop once the face count is at most this value */
  bool preserve_boundary;  /* do not collapse edges touching the boundary */
  bool verify_watertight;  /* reject a non-closed output (default: true) */
} tvdb_simplify_options_t;

tvdb_status_t tvdb_mesh_simplify_ex(const tvdb_triangle_mesh *in,
                                     const tvdb_simplify_options_t *options,
                                     tvdb_triangle_mesh *out,
                                     tvdb_arena_allocator_t *arena,
                                     tvdb_error_t *err);

/* Convenience wrapper: preserve boundary, verify closure, no error context. */
bool tvdb_mesh_simplify(const tvdb_triangle_mesh *in, size_t target_faces,
                         tvdb_triangle_mesh *out, tvdb_arena_allocator_t *arena);

#ifdef __cplusplus
}
#endif
