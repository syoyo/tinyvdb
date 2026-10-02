#pragma once
#include "tinyvdb_ops.h"
#include "tinyvdb_tree.h"
#ifdef __cplusplus
extern "C" {
#endif

/* All constructors require distinct initialized owning outputs, use libc,
 * and preserve source/output/report on failure. Float trees only. Budgets of
 * zero select 1,000,000 coordinates/cells; budget exhaustion is an error.
 * Index samples are at integer coordinates mapped by the complete transform.
 * No dense bounding-box array is allocated. */
typedef enum {
  TVDB_SAMPLE_NEAREST = 0,
  TVDB_SAMPLE_LINEAR = 1
} tvdb_tree_sampler_t;
/* Scalar values (including stored inactive values) are sampled in world space.
 * An output sample is active if any nonzero-weight input tap is active.
 * Nonbackground inactive values are retained and exactly pruned. Output uses
 * the standard float 5/4/3 hierarchy. Level sets are not redistanced here. */
tvdb_status_t tvdb_grid_resample(const tvdb_grid_t* source,
                                 const tvdb_transform_t* target,
                                 tvdb_tree_sampler_t sampler, size_t max_voxels,
                                 tvdb_grid_t* out, tvdb_error_t* err);

/* Indexed classic MC over stored negative regions and their boundaries,
 * including inactive tiles; active state does not clip the surface. Replaces
 * an owning mesh, with outward winding for values below isovalue. All affine
 * transforms, including reflections, are supported. adaptivity is a maximum
 * world-space vertex displacement (0 disables clustering); shared global
 * clusters remove faces with repeated indices. Classic ambiguities/clustering
 * do not guarantee manifoldness or preserve topology. max_cells also bounds
 * boundary scan work (32 times this budget), so huge tile faces can fail
 * explicitly. */
tvdb_status_t tvdb_grid_volume_to_mesh(const tvdb_grid_t* source,
                                       float isovalue, double adaptivity,
                                       size_t max_cells,
                                       tvdb_triangle_mesh* out,
                                       tvdb_error_t* err);

typedef struct {
  size_t surface_cells, candidate_voxels, active_voxels;
  double max_distance;
} tvdb_level_set_rebuild_result_t;
/* Reconstruct the piecewise-linear isosurface, then closest-triangle world
 * distances using a BVH. Expands/trims topology and fills inactive signs.
 * Closed, resolved narrow-band inputs with positive exterior background only;
 * affine columns must be orthogonal and have equal lengths. Widths are positive
 * world distances, inside_width is a positive magnitude. This geometric
 * rebuild has no iterative convergence budget and cannot repair unresolved or
 * open surfaces. Tracking is a rebuild after edits; it does not advect a grid.
 * Active values satisfy -inside_width < value < outside_width. */
tvdb_status_t tvdb_grid_level_set_rebuild(
    const tvdb_grid_t* source, float isovalue, float outside_width,
    float inside_width, size_t max_voxels, tvdb_grid_t* out,
    tvdb_level_set_rebuild_result_t* result, tvdb_error_t* err);
tvdb_status_t tvdb_grid_level_set_track(const tvdb_grid_t* source,
                                        float outside_width, float inside_width,
                                        size_t max_voxels, tvdb_grid_t* out,
                                        tvdb_level_set_rebuild_result_t* result,
                                        tvdb_error_t* err);

typedef enum {
  TVDB_BOUNDARY_DIRICHLET = 0,
  TVDB_BOUNDARY_NEUMANN = 1
} tvdb_boundary_kind_t;
/* Called once per missing-neighbor face. Dirichlet value is at that neighbor's
 * center; Neumann value is outward k*du/dn at the half-cell face. Return zero
 * to fail. NULL callback selects zero Dirichlet. Coordinates use int64 so
 * neighbors outside int32 remain representable. */
typedef int (*tvdb_sparse_boundary_fn)(const int32_t coord[3],
                                       const int64_t neighbor[3],
                                       tvdb_boundary_kind_t* kind,
                                       double* value, void* user);
/* Positive finite face conductivity, called once per undirected active edge
 * and once per boundary face; the same coefficient is used by both rows. */
typedef double (*tvdb_sparse_coefficient_fn)(const int32_t coord[3],
                                             const int64_t neighbor[3],
                                             void* user);
typedef struct {
  int max_iterations;
  double tolerance; /* relative L2 residual; includes returned float rounding */
  size_t max_voxels;
  tvdb_sparse_boundary_fn boundary;
  tvdb_sparse_coefficient_fn coefficient;
  void* user;
} tvdb_sparse_poisson_options_t;
/* Solve -div(k grad u)=rhs on active topology with Jacobi-preconditioned CG in
 * double. Orthogonal affine axes may have different spacing; shear is rejected.
 * Active tiles expand within max_voxels. Each pure-Neumann connected component
 * requires compatible summed RHS/flux (rounding tolerance 1e-10 of L1
 * magnitude) and gets zero-mean u; disconnected components are handled
 * independently. A zero RHS needs no iterations. Iteration exhaustion commits a
 * finite iterate with converged=false; invalid/OOM/breakdown preserves outputs.
 * Inactive output values/background are zero, independent of boundary
 * callbacks. */
tvdb_status_t tvdb_grid_solve_poisson(
    const tvdb_grid_t* rhs, const tvdb_sparse_poisson_options_t* options,
    tvdb_grid_t* out, tvdb_poisson_result_t* result, tvdb_error_t* err);
#ifdef __cplusplus
}
#endif
