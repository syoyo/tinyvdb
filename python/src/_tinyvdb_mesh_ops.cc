/*
 * _tinyvdb_mesh_ops.cc — C-API wrappers for tinyvdb_mesh.h / tinyvdb_ops.h
 *
 * Compiled as C++11, exposes C-API functions callable from _tinyvdb.c.
 * All data is exchanged via flat arrays (float*, uint32_t*) and sizes.
 */

#include "tinyvdb_mesh.h"
#include "tinyvdb_ops.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_ray.h"
#include "tinyvdb_tsdf.h"
#include "tinyvdb_topology.h"
#include "tinyvdb_sparse_tree.h"
#include "tinyvdb_autograd.h"
#include "tinyvdb_levelset.h"
#include "tinyvdb_stats.h"
#include "tinyvdb_grid_index.h"
#include "tinyvdb_render.h"

#include <cmath>
#include <cstring>
#include <cstdlib>
#include <vector>
#include <cstdio>

/* Thread-local error message buffer */
static thread_local char s_error_msg[512] = {0};

extern "C" {

const char *tvdb_py_last_error(void) { return s_error_msg; }

/* ======================================================================== */
/*  Helpers                                                                  */
/* ======================================================================== */

static tvdb_dense_grid make_grid(const float *data, int nx, int ny, int nz,
                                 float voxel_size, float ox, float oy,
                                 float oz) {
    tvdb_dense_grid g;
    tvdb_dense_grid_init(&g, nx, ny, nz);
    g.ox = ox; g.oy = oy; g.oz = oz;
    g.voxel_size = voxel_size;
    memcpy(g.data, data, (size_t)nx * ny * nz * sizeof(float));
    return g;
}

static tvdb_dense_vec_grid make_vec_grid(const float *data, int nx, int ny,
                                         int nz, float voxel_size,
                                         float ox, float oy, float oz) {
    tvdb_dense_vec_grid g;
    tvdb_dense_vec_grid_init(&g, nx, ny, nz);
    g.ox = ox; g.oy = oy; g.oz = oz;
    g.voxel_size = voxel_size;
    memcpy(g.data, data, (size_t)nx * ny * nz * 3 * sizeof(float));
    return g;
}

/* Copy DenseGrid data out to caller-allocated buffer. */
static void export_grid(const tvdb_dense_grid *g, float **out_data,
                        int *nx, int *ny, int *nz, float *voxel_size,
                        float *ox, float *oy, float *oz) {
    *nx = g->nx; *ny = g->ny; *nz = g->nz;
    *voxel_size = g->voxel_size;
    *ox = g->ox; *oy = g->oy; *oz = g->oz;
    size_t n = (size_t)g->nx * g->ny * g->nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, g->data, n * sizeof(float));
}

/* ======================================================================== */
/*  Mesh API                                                                */
/* ======================================================================== */

int tvdb_py_mesh_to_sdf(const float *verts, size_t nv,
                        const uint32_t *tris, size_t nt,
                        float voxel_size, float band_width, int sign_method,
                        float **out_data, int *nx, int *ny, int *nz,
                        float *out_voxel_size,
                        float *ox, float *oy, float *oz) {
    tvdb_triangle_mesh mesh;
    tvdb_triangle_mesh_init(&mesh);
    mesh.vertex_count = mesh.vertex_capacity = nv;
    mesh.vertices = (tvdb_vec3f*)malloc(nv * sizeof(tvdb_vec3f));
    memcpy(mesh.vertices, verts, nv * sizeof(tvdb_vec3f));
    mesh.face_count = mesh.face_capacity = nt;
    mesh.faces = (tvdb_triangle*)malloc(nt * sizeof(tvdb_triangle));
    memcpy(mesh.faces, tris, nt * sizeof(tvdb_triangle));

    tvdb_dense_grid grid;
    grid.data = NULL; // Initialized by tvdb_mesh_to_sdf_vdb
    tvdb_arena_allocator_t* arena = NULL;
    bool ok = tvdb_mesh_to_sdf_vdb(&mesh, voxel_size, band_width, &grid,
                                   (tvdb_sign_method)sign_method, arena);
    tvdb_triangle_mesh_free(&mesh);

    if (!ok) {
        snprintf(s_error_msg, sizeof(s_error_msg), "MeshToSDF_VDB failed");
        return -1;
    }
    export_grid(&grid, out_data, nx, ny, nz, out_voxel_size, ox, oy, oz);
    tvdb_dense_grid_free(&grid);
    return 0;
}

int tvdb_py_sdf_to_mesh(const float *data, int nx, int ny, int nz,
                        float voxel_size, float ox, float oy, float oz,
                        float isovalue,
                        float **out_verts, size_t *out_nv,
                        uint32_t **out_tris, size_t *out_nt) {
    tvdb_dense_grid grid = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_triangle_mesh mesh;
    tvdb_triangle_mesh_init(&mesh);
    tvdb_arena_allocator_t* arena = NULL;
    bool ok = tvdb_sdf_to_mesh(&grid, isovalue, &mesh, arena);
    tvdb_dense_grid_free(&grid);

    if (!ok) {
        snprintf(s_error_msg, sizeof(s_error_msg), "SDFToMesh failed");
        return -1;
    }
    *out_nv = mesh.vertex_count;
    *out_nt = mesh.face_count;
    *out_verts = (float *)malloc(*out_nv * 3 * sizeof(float));
    *out_tris = (uint32_t *)malloc(*out_nt * 3 * sizeof(uint32_t));
    if (!*out_verts || !*out_tris) {
        free(*out_verts);
        free(*out_tris);
        snprintf(s_error_msg, sizeof(s_error_msg), "malloc failed");
        return -1;
    }
    memcpy(*out_verts, mesh.vertices, *out_nv * 3 * sizeof(float));
    memcpy(*out_tris, mesh.faces, *out_nt * 3 * sizeof(uint32_t));
    tvdb_triangle_mesh_free(&mesh);
    return 0;
}

int tvdb_py_make_manifold(const float *verts, size_t nv,
                          const uint32_t *tris, size_t nt,
                          double resolution, double isovalue, int sign_method,
                          float **out_verts, size_t *out_nv,
                          uint32_t **out_tris, size_t *out_nt) {
    tvdb_triangle_mesh input;
    tvdb_triangle_mesh_init(&input);
    input.vertex_count = input.vertex_capacity = nv;
    input.vertices = (tvdb_vec3f*)malloc(nv * sizeof(tvdb_vec3f));
    memcpy(input.vertices, verts, nv * sizeof(tvdb_vec3f));
    input.face_count = input.face_capacity = nt;
    input.faces = (tvdb_triangle*)malloc(nt * sizeof(tvdb_triangle));
    memcpy(input.faces, tris, nt * sizeof(tvdb_triangle));

    tvdb_triangle_mesh output;
    tvdb_triangle_mesh_init(&output);
    tvdb_arena_allocator_t* arena = NULL;
    bool ok = tvdb_make_manifold_vdb(&input, resolution, isovalue, &output,
                                     (tvdb_sign_method)sign_method, arena);
    tvdb_triangle_mesh_free(&input);
    if (!ok) {
        snprintf(s_error_msg, sizeof(s_error_msg), "MakeManifold_VDB failed");
        return -1;
    }
    *out_nv = output.vertex_count;
    *out_nt = output.face_count;
    *out_verts = (float *)malloc(*out_nv * 3 * sizeof(float));
    *out_tris = (uint32_t *)malloc(*out_nt * 3 * sizeof(uint32_t));
    if (!*out_verts || !*out_tris) {
        free(*out_verts); free(*out_tris);
        snprintf(s_error_msg, sizeof(s_error_msg), "malloc failed");
        return -1;
    }
    memcpy(*out_verts, output.vertices, *out_nv * 3 * sizeof(float));
    memcpy(*out_tris, output.faces, *out_nt * 3 * sizeof(uint32_t));
    tvdb_triangle_mesh_free(&output);
    return 0;
}

/* ======================================================================== */
/*  Morphology / filtering — in-place on caller's buffer                     */
/* ======================================================================== */

#define INPLACE_ITER(FN)                                                      \
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);  \
    FN(&g, iterations);                                                       \
    memcpy(data, g.data, (size_t)nx * ny * nz * sizeof(float));               \
    tvdb_dense_grid_free(&g);                                                 \
    return 0

int tvdb_py_dilate(float *data, int nx, int ny, int nz,
                   float voxel_size, float ox, float oy, float oz, int iterations) {
    INPLACE_ITER(tvdb_dilate);
}
int tvdb_py_erode(float *data, int nx, int ny, int nz,
                  float voxel_size, float ox, float oy, float oz, int iterations) {
    INPLACE_ITER(tvdb_erode);
}
int tvdb_py_open(float *data, int nx, int ny, int nz,
                 float voxel_size, float ox, float oy, float oz, int iterations) {
    INPLACE_ITER(tvdb_open);
}
int tvdb_py_close(float *data, int nx, int ny, int nz,
                  float voxel_size, float ox, float oy, float oz, int iterations) {
    INPLACE_ITER(tvdb_close);
}
#undef INPLACE_ITER

int tvdb_py_gaussian_filter(float *data, int nx, int ny, int nz,
                            float voxel_size, float ox, float oy, float oz,
                            int width, int iterations) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_gaussian_filter(&g, width, iterations);
    memcpy(data, g.data, (size_t)nx * ny * nz * sizeof(float));
    tvdb_dense_grid_free(&g);
    return 0;
}
int tvdb_py_mean_filter(float *data, int nx, int ny, int nz,
                        float voxel_size, float ox, float oy, float oz,
                        int width, int iterations) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mean_filter(&g, width, iterations);
    memcpy(data, g.data, (size_t)nx * ny * nz * sizeof(float));
    tvdb_dense_grid_free(&g);
    return 0;
}
int tvdb_py_laplacian_filter(float *data, int nx, int ny, int nz,
                             float voxel_size, float ox, float oy, float oz,
                             int iterations) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_laplacian_filter(&g, iterations);
    memcpy(data, g.data, (size_t)nx * ny * nz * sizeof(float));
    tvdb_dense_grid_free(&g);
    return 0;
}

/* ======================================================================== */
/*  CSG — same dimensions assumed; result allocated by us                    */
/* ======================================================================== */

#define RUN_CSG(FN)                                                           \
    tvdb_dense_grid ga = make_grid(a, nx, ny, nz, voxel_size, ox, oy, oz);    \
    tvdb_dense_grid gb = make_grid(b, nx, ny, nz, voxel_size, ox, oy, oz);    \
    tvdb_dense_grid gr;                                                       \
    tvdb_dense_grid_init(&gr, nx, ny, nz);                                    \
    gr.voxel_size = voxel_size; gr.ox = ox; gr.oy = oy; gr.oz = oz;           \
    FN(&ga, &gb, &gr);                                                        \
    size_t _n = (size_t)nx * ny * nz;                                         \
    *out_data = (float *)malloc(_n * sizeof(float));                          \
    if (*out_data) memcpy(*out_data, gr.data, _n * sizeof(float));            \
    tvdb_dense_grid_free(&ga); tvdb_dense_grid_free(&gb); tvdb_dense_grid_free(&gr); \
    return *out_data ? 0 : -1

int tvdb_py_csg_union(const float *a, const float *b, int nx, int ny, int nz,
                      float voxel_size, float ox, float oy, float oz,
                      float **out_data) {
    RUN_CSG(tvdb_csg_union);
}
int tvdb_py_csg_intersection(const float *a, const float *b, int nx, int ny, int nz,
                             float voxel_size, float ox, float oy, float oz,
                             float **out_data) {
    RUN_CSG(tvdb_csg_intersection);
}
int tvdb_py_csg_difference(const float *a, const float *b, int nx, int ny, int nz,
                           float voxel_size, float ox, float oy, float oz,
                           float **out_data) {
    RUN_CSG(tvdb_csg_difference);
}
#undef RUN_CSG

/* ======================================================================== */
/*  Measurement                                                              */
/* ======================================================================== */

float tvdb_py_surface_area(const float *data, int nx, int ny, int nz,
                           float voxel_size, float ox, float oy, float oz) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    float r = tvdb_surface_area(&g);
    tvdb_dense_grid_free(&g);
    return r;
}
float tvdb_py_volume(const float *data, int nx, int ny, int nz,
                     float voxel_size, float ox, float oy, float oz) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    float r = tvdb_volume(&g);
    tvdb_dense_grid_free(&g);
    return r;
}

/* ======================================================================== */
/*  Differential operators                                                   */
/* ======================================================================== */

int tvdb_py_gradient(const float *data, int nx, int ny, int nz,
                     float voxel_size, float ox, float oy, float oz,
                     float **out_vec_data) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_vec_grid out;
    tvdb_dense_vec_grid_init(&out, nx, ny, nz);
    out.voxel_size = voxel_size; out.ox = ox; out.oy = oy; out.oz = oz;
    tvdb_gradient(&g, &out);
    size_t n = (size_t)nx * ny * nz * 3;
    *out_vec_data = (float *)malloc(n * sizeof(float));
    if (*out_vec_data) memcpy(*out_vec_data, out.data, n * sizeof(float));
    tvdb_dense_grid_free(&g); tvdb_dense_vec_grid_free(&out);
    return *out_vec_data ? 0 : -1;
}

int tvdb_py_divergence(const float *vec_data, int nx, int ny, int nz,
                       float voxel_size, float ox, float oy, float oz,
                       float **out_data) {
    tvdb_dense_vec_grid v = make_vec_grid(vec_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_grid out;
    tvdb_dense_grid_init(&out, nx, ny, nz);
    out.voxel_size = voxel_size; out.ox = ox; out.oy = oy; out.oz = oz;
    tvdb_divergence(&v, &out);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, out.data, n * sizeof(float));
    tvdb_dense_vec_grid_free(&v); tvdb_dense_grid_free(&out);
    return *out_data ? 0 : -1;
}

int tvdb_py_laplacian(const float *data, int nx, int ny, int nz,
                      float voxel_size, float ox, float oy, float oz,
                      float **out_data) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_grid out;
    tvdb_dense_grid_init(&out, nx, ny, nz);
    out.voxel_size = voxel_size; out.ox = ox; out.oy = oy; out.oz = oz;
    tvdb_laplacian(&g, &out);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, out.data, n * sizeof(float));
    tvdb_dense_grid_free(&g); tvdb_dense_grid_free(&out);
    return *out_data ? 0 : -1;
}

int tvdb_py_curl(const float *vec_data, int nx, int ny, int nz,
                 float voxel_size, float ox, float oy, float oz,
                 float **out_vec_data) {
    tvdb_dense_vec_grid v = make_vec_grid(vec_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_vec_grid out;
    tvdb_dense_vec_grid_init(&out, nx, ny, nz);
    out.voxel_size = voxel_size; out.ox = ox; out.oy = oy; out.oz = oz;
    tvdb_curl(&v, &out);
    size_t n = (size_t)nx * ny * nz * 3;
    *out_vec_data = (float *)malloc(n * sizeof(float));
    if (*out_vec_data) memcpy(*out_vec_data, out.data, n * sizeof(float));
    tvdb_dense_vec_grid_free(&v); tvdb_dense_vec_grid_free(&out);
    return *out_vec_data ? 0 : -1;
}

/* ======================================================================== */
/*  Advection / Poisson                                                      */
/* ======================================================================== */

int tvdb_py_advect(const float *field_data, const float *vel_data,
                   int nx, int ny, int nz, float voxel_size,
                   float ox, float oy, float oz, float dt,
                   float **out_data) {
    tvdb_dense_grid f = make_grid(field_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_vec_grid v = make_vec_grid(vel_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_grid out;
    tvdb_dense_grid_init(&out, nx, ny, nz);
    out.voxel_size = voxel_size; out.ox = ox; out.oy = oy; out.oz = oz;
    tvdb_advect_semi_lagrangian(&f, &v, dt, &out);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, out.data, n * sizeof(float));
    tvdb_dense_grid_free(&f); tvdb_dense_vec_grid_free(&v); tvdb_dense_grid_free(&out);
    return *out_data ? 0 : -1;
}

int tvdb_py_advect_scheme(const float *field_data, const float *vel_data,
                          int nx, int ny, int nz, float voxel_size,
                          float ox, float oy, float oz, float dt, int scheme, int clamp,
                          float **out_data) {
    tvdb_dense_grid f = make_grid(field_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_vec_grid v = make_vec_grid(vel_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_grid out;
    tvdb_dense_grid_init(&out, nx, ny, nz);
    out.voxel_size = voxel_size; out.ox = ox; out.oy = oy; out.oz = oz;
    tvdb_advect(&f, &v, dt, scheme, clamp, &out);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, out.data, n * sizeof(float));
    tvdb_dense_grid_free(&f); tvdb_dense_vec_grid_free(&v); tvdb_dense_grid_free(&out);
    return *out_data ? 0 : -1;
}

int tvdb_py_solve_poisson(const float *rhs_data, int nx, int ny, int nz,
                          float voxel_size, float ox, float oy, float oz,
                          int max_iters, float tolerance,
                          float **out_data, int *out_iters) {
    tvdb_dense_grid rhs = make_grid(rhs_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_grid x;
    tvdb_dense_grid_init(&x, nx, ny, nz);
    x.voxel_size = voxel_size; x.ox = ox; x.oy = oy; x.oz = oz;
    int iters = tvdb_solve_poisson(&rhs, &x, max_iters, tolerance);
    if (out_iters) *out_iters = iters;
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, x.data, n * sizeof(float));
    tvdb_dense_grid_free(&rhs); tvdb_dense_grid_free(&x);
    return *out_data ? 0 : -1;
}

// fp64 internals variant of solve_poisson.
int tvdb_py_solve_poisson_d(const float *rhs_data, int nx, int ny, int nz,
                            float voxel_size, float ox, float oy, float oz,
                            int max_iters, double tolerance,
                            float **out_data, int *out_iters) {
    tvdb_dense_grid rhs = make_grid(rhs_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_grid x;
    tvdb_dense_grid_init(&x, nx, ny, nz);
    x.voxel_size = voxel_size; x.ox = ox; x.oy = oy; x.oz = oz;
    int iters = tvdb_solve_poisson_d(&rhs, &x, max_iters, tolerance);
    if (out_iters) *out_iters = iters;
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, x.data, n * sizeof(float));
    tvdb_dense_grid_free(&rhs); tvdb_dense_grid_free(&x);
    return *out_data ? 0 : -1;
}

// Fast sweeping: redistance an SDF on a dense grid. In-place on a copy so
// the Python caller gets ownership of `out_data`.
int tvdb_py_fast_sweeping(const float *data, int nx, int ny, int nz,
                          float voxel_size, float ox, float oy, float oz,
                          float frozen_band, int max_iters, float tol,
                          float **out_data, int *out_iters) {
    size_t n = (size_t)nx * ny * nz;
    tvdb_dense_grid g;
    tvdb_dense_grid_init(&g, nx, ny, nz);
    g.voxel_size = voxel_size; g.ox = ox; g.oy = oy; g.oz = oz;
    if (data) memcpy(g.data, data, n * sizeof(float));
    int iters = tvdb_fast_sweeping(&g, frozen_band, max_iters, tol);
    if (out_iters) *out_iters = iters;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, g.data, n * sizeof(float));
    tvdb_dense_grid_free(&g);
    return *out_data ? 0 : -1;
}

/* ======================================================================== */
/*  Stubs for advanced ops still referenced by _tinyvdb.c but not yet        */
/*  implemented in tinyvdb. Returning -1 keeps the link clean; calling them  */
/*  from Python surfaces a tvdb_py_last_error() message.                     */
/* ======================================================================== */

int tvdb_py_ray_cast_sdf(const float *data, int nx, int ny, int nz,
                         float voxel_size, float ox, float oy, float oz,
                         float rx, float ry, float rz,
                         float dx, float dy, float dz, float max_t,
                         int *out_hit, float *out_t,
                         float *out_px, float *out_py, float *out_pz,
                         float *out_nx, float *out_ny, float *out_nz) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);

    // Normalize direction.
    float dlen = std::sqrt(dx * dx + dy * dy + dz * dz);
    if (dlen < 1e-30f) {
        tvdb_dense_grid_free(&g);
        *out_hit = 0; return 0;
    }
    float ndx = dx / dlen, ndy = dy / dlen, ndz = dz / dlen;

    tvdb_ray ray;
    ray.origin.x = rx; ray.origin.y = ry; ray.origin.z = rz;
    ray.dir.x = ndx;   ray.dir.y = ndy;   ray.dir.z = ndz;
    ray.tmin = 0.0f;
    ray.tmax = max_t;

    // Use segments-along-ray with isovalue=0 to find the first inside run.
    // step_count proportional to grid extent for adequate sampling.
    int max_dim = nx > ny ? nx : ny; if (nz > max_dim) max_dim = nz;
    size_t steps = (size_t)(max_dim * 4) + 64;
    float pair[2];
    size_t n = tvdb_segments_along_ray(&g, &ray, 0.0f, steps, pair, 1);
    if (n == 0) {
        tvdb_dense_grid_free(&g);
        *out_hit = 0; return 0;
    }
    float t_hit = pair[0];
    float hx = rx + t_hit * ndx;
    float hy = ry + t_hit * ndy;
    float hz = rz + t_hit * ndz;

    // Estimate normal via central differences of the SDF near the hit.
    float h = voxel_size;
    float fxp = tvdb_sample_trilinear_dense(&g, hx + h, hy, hz);
    float fxm = tvdb_sample_trilinear_dense(&g, hx - h, hy, hz);
    float fyp = tvdb_sample_trilinear_dense(&g, hx, hy + h, hz);
    float fym = tvdb_sample_trilinear_dense(&g, hx, hy - h, hz);
    float fzp = tvdb_sample_trilinear_dense(&g, hx, hy, hz + h);
    float fzm = tvdb_sample_trilinear_dense(&g, hx, hy, hz - h);
    float gx = (fxp - fxm), gy = (fyp - fym), gz = (fzp - fzm);
    float gl = std::sqrt(gx * gx + gy * gy + gz * gz);
    if (gl > 1e-30f) { gx /= gl; gy /= gl; gz /= gl; }

    *out_hit = 1;
    *out_t = t_hit;
    *out_px = hx; *out_py = hy; *out_pz = hz;
    *out_nx = gx; *out_ny = gy; *out_nz = gz;
    tvdb_dense_grid_free(&g);
    return 0;
}

int tvdb_py_particles_to_sdf(const float *positions, const float *radii, size_t n,
                             float voxel_size, float band_width,
                             float **out_data, int *out_nx, int *out_ny, int *out_nz,
                             float *out_voxel_size,
                             float *out_ox, float *out_oy, float *out_oz) {
    if (n == 0 || voxel_size <= 0.0f || band_width <= 0.0f) {
        snprintf(s_error_msg, sizeof(s_error_msg), "particles_to_sdf: empty/invalid input");
        return -1;
    }
    // World-space bbox padded by max radius + band.
    float bb[6] = { positions[0], positions[1], positions[2],
                    positions[0], positions[1], positions[2] };
    float max_r = radii[0];
    for (size_t i = 0; i < n; ++i) {
        float px = positions[i * 3 + 0], py = positions[i * 3 + 1], pz = positions[i * 3 + 2];
        if (px < bb[0]) bb[0] = px; if (px > bb[3]) bb[3] = px;
        if (py < bb[1]) bb[1] = py; if (py > bb[4]) bb[4] = py;
        if (pz < bb[2]) bb[2] = pz; if (pz > bb[5]) bb[5] = pz;
        if (radii[i] > max_r) max_r = radii[i];
    }
    float pad = max_r + band_width;
    bb[0] -= pad; bb[1] -= pad; bb[2] -= pad;
    bb[3] += pad; bb[4] += pad; bb[5] += pad;

    int nx = (int)std::ceil((bb[3] - bb[0]) / voxel_size);
    int ny = (int)std::ceil((bb[4] - bb[1]) / voxel_size);
    int nz = (int)std::ceil((bb[5] - bb[2]) / voxel_size);
    if (nx < 1) nx = 1; if (ny < 1) ny = 1; if (nz < 1) nz = 1;

    size_t total = (size_t)nx * ny * nz;
    float *out = (float *)malloc(total * sizeof(float));
    if (!out) {
        snprintf(s_error_msg, sizeof(s_error_msg), "particles_to_sdf: malloc failed");
        return -1;
    }
    // Initialize to +band (far outside).
    for (size_t i = 0; i < total; ++i) out[i] = band_width;

    // For each voxel, take min over particles of (||v - p|| - r), clamped to ±band.
    // O(V*N); acceptable for moderate inputs.
    for (int iz = 0; iz < nz; ++iz) {
      float wz = bb[2] + ((float)iz + 0.5f) * voxel_size;
      for (int iy = 0; iy < ny; ++iy) {
        float wy = bb[1] + ((float)iy + 0.5f) * voxel_size;
        for (int ix = 0; ix < nx; ++ix) {
          float wx = bb[0] + ((float)ix + 0.5f) * voxel_size;
          float best = band_width;
          for (size_t p = 0; p < n; ++p) {
            float dx = wx - positions[p * 3 + 0];
            float dy = wy - positions[p * 3 + 1];
            float dz = wz - positions[p * 3 + 2];
            float d = std::sqrt(dx * dx + dy * dy + dz * dz) - radii[p];
            if (d < best) best = d;
          }
          if (best < -band_width) best = -band_width;
          out[(size_t)((iz * ny + iy) * nx + ix)] = best;
        }
      }
    }
    *out_data = out;
    *out_nx = nx; *out_ny = ny; *out_nz = nz;
    *out_voxel_size = voxel_size;
    *out_ox = bb[0]; *out_oy = bb[1]; *out_oz = bb[2];
    return 0;
}
int tvdb_py_volume_to_spheres(const float *data, int nx, int ny, int nz,
                              float voxel_size, float ox, float oy, float oz,
                              float min_radius, int max_spheres, float overlap,
                              float **out_centers, float **out_radii, size_t *out_count) {
    // Greedy medial-axis cover: at each step, find the voxel whose SDF is most
    // negative (deepest interior point), place a sphere with radius = |sdf|,
    // mark all voxels within (1 - overlap) * radius as "taken" (set sdf to +inf
    // so they won't be picked again). Stop when sphere count reaches max or
    // remaining minimum is above min_radius.
    if (!data || nx <= 0 || ny <= 0 || nz <= 0 || voxel_size <= 0.0f) {
        snprintf(s_error_msg, sizeof(s_error_msg), "volume_to_spheres: invalid input");
        return -1;
    }
    const size_t total = (size_t)nx * ny * nz;
    float *work = (float *)malloc(total * sizeof(float));
    if (!work) {
        snprintf(s_error_msg, sizeof(s_error_msg), "volume_to_spheres: malloc failed");
        return -1;
    }
    memcpy(work, data, total * sizeof(float));

    std::vector<float> centers, radii;
    const float keep_factor = 1.0f - (overlap < 0.0f ? 0.0f : (overlap > 1.0f ? 1.0f : overlap));

    for (int step = 0; step < max_spheres; ++step) {
        // Find min-value voxel.
        size_t best_idx = 0;
        float best_v = 0.0f;
        for (size_t i = 0; i < total; ++i) {
            if (work[i] < best_v) { best_v = work[i]; best_idx = i; }
        }
        if (best_v >= 0.0f) break;
        float radius_w = -best_v;
        if (radius_w < min_radius) break;

        int bx = (int)(best_idx % (size_t)nx);
        int by = (int)((best_idx / (size_t)nx) % (size_t)ny);
        int bz = (int)(best_idx / (size_t)(nx * ny));
        float cx_w = ox + ((float)bx + 0.5f) * voxel_size;
        float cy_w = oy + ((float)by + 0.5f) * voxel_size;
        float cz_w = oz + ((float)bz + 0.5f) * voxel_size;
        centers.push_back(cx_w); centers.push_back(cy_w); centers.push_back(cz_w);
        radii.push_back(radius_w);

        // Mark as taken: any voxel within keep_factor * radius gets +inf.
        float kr = keep_factor * radius_w;
        float kr_sq = kr * kr;
        int rad_v = (int)std::ceil(kr / voxel_size) + 1;
        int z0 = bz - rad_v < 0 ? 0 : bz - rad_v;
        int z1 = bz + rad_v + 1 > nz ? nz : bz + rad_v + 1;
        int y0 = by - rad_v < 0 ? 0 : by - rad_v;
        int y1 = by + rad_v + 1 > ny ? ny : by + rad_v + 1;
        int x0 = bx - rad_v < 0 ? 0 : bx - rad_v;
        int x1 = bx + rad_v + 1 > nx ? nx : bx + rad_v + 1;
        for (int iz = z0; iz < z1; ++iz)
          for (int iy = y0; iy < y1; ++iy)
            for (int ix = x0; ix < x1; ++ix) {
              float wx = ox + ((float)ix + 0.5f) * voxel_size - cx_w;
              float wy = oy + ((float)iy + 0.5f) * voxel_size - cy_w;
              float wz = oz + ((float)iz + 0.5f) * voxel_size - cz_w;
              if (wx * wx + wy * wy + wz * wz <= kr_sq) {
                work[(size_t)((iz * ny + iy) * nx + ix)] = INFINITY;
              }
            }
    }
    free(work);

    *out_count = radii.size();
    if (*out_count == 0) {
        *out_centers = (float *)malloc(1);  // dummy non-null pointer
        *out_radii   = (float *)malloc(1);
        return 0;
    }
    size_t cb = centers.size() * sizeof(float);
    size_t rb = radii.size() * sizeof(float);
    *out_centers = (float *)malloc(cb);
    *out_radii   = (float *)malloc(rb);
    if (!*out_centers || !*out_radii) {
        free(*out_centers); free(*out_radii);
        snprintf(s_error_msg, sizeof(s_error_msg), "volume_to_spheres: malloc failed");
        return -1;
    }
    memcpy(*out_centers, centers.data(), cb);
    memcpy(*out_radii,   radii.data(),   rb);
    return 0;
}
int tvdb_py_fracture(const float *data, int nx, int ny, int nz,
                     float voxel_size, float ox, float oy, float oz,
                     const float **cutters, int n_cutters,
                     float ***out_pieces, int *out_count) {
    // Output N+1 pieces:
    //   piece[i]   = csg_intersection(input, cutter[i])  for i in [0, N)
    //   piece[N]   = csg_difference(input, csg_union(cutter[0..N)))   (residual)
    // All pieces share the input grid's dimensions / origin / voxel_size.
    (void)voxel_size; (void)ox; (void)oy; (void)oz;
    if (!data || nx <= 0 || ny <= 0 || nz <= 0) {
        snprintf(s_error_msg, sizeof(s_error_msg), "fracture: invalid input");
        return -1;
    }
    if (n_cutters < 0) {
        snprintf(s_error_msg, sizeof(s_error_msg), "fracture: negative cutter count");
        return -1;
    }
    const size_t total = (size_t)nx * ny * nz;
    int n_pieces = n_cutters + 1;
    float **pieces = (float **)malloc((size_t)n_pieces * sizeof(float *));
    if (!pieces) {
        snprintf(s_error_msg, sizeof(s_error_msg), "fracture: malloc failed");
        return -1;
    }
    for (int i = 0; i < n_pieces; ++i) pieces[i] = NULL;

    // Per-cutter intersection.
    for (int c = 0; c < n_cutters; ++c) {
        float *p = (float *)malloc(total * sizeof(float));
        if (!p) goto fail;
        for (size_t k = 0; k < total; ++k) {
            float a = data[k];
            float b = cutters[c][k];
            p[k] = a > b ? a : b;  // SDF intersection = pointwise max
        }
        pieces[c] = p;
    }

    // Residual: input minus union(all cutters) = max(input, -union).
    {
        float *uni = NULL;
        if (n_cutters > 0) {
            uni = (float *)malloc(total * sizeof(float));
            if (!uni) goto fail;
            // Start with first cutter, then min with the rest.
            for (size_t k = 0; k < total; ++k) uni[k] = cutters[0][k];
            for (int c = 1; c < n_cutters; ++c) {
                for (size_t k = 0; k < total; ++k) {
                    if (cutters[c][k] < uni[k]) uni[k] = cutters[c][k];
                }
            }
        }
        float *p = (float *)malloc(total * sizeof(float));
        if (!p) { free(uni); goto fail; }
        if (uni) {
            for (size_t k = 0; k < total; ++k) {
                float a = data[k], nb = -uni[k];
                p[k] = a > nb ? a : nb;
            }
            free(uni);
        } else {
            // No cutters: residual is the input itself.
            memcpy(p, data, total * sizeof(float));
        }
        pieces[n_pieces - 1] = p;
    }

    *out_pieces = pieces;
    *out_count = n_pieces;
    return 0;

fail:
    for (int i = 0; i < n_pieces; ++i) free(pieces[i]);
    free(pieces);
    snprintf(s_error_msg, sizeof(s_error_msg), "fracture: malloc failed");
    return -1;
}

/* ======================================================================== */
/*  Phase 4-6: sampling, TSDF, topology, pooling                             */
/* ======================================================================== */

int tvdb_py_sample_trilinear(const float *data, int nx, int ny, int nz,
                             float voxel_size, float ox, float oy, float oz,
                             const float *points, size_t npts,
                             float **out_vals) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    *out_vals = (float *)malloc(npts * sizeof(float));
    if (!*out_vals) {
        tvdb_dense_grid_free(&g);
        snprintf(s_error_msg, sizeof(s_error_msg), "sample_trilinear: malloc failed");
        return -1;
    }
    tvdb_sample_trilinear_dense_batch(&g, (const tvdb_vec3f *)points, npts, *out_vals);
    tvdb_dense_grid_free(&g);
    return 0;
}

int tvdb_py_sample_quadratic(const float *data, int nx, int ny, int nz,
                             float voxel_size, float ox, float oy, float oz,
                             const float *points, size_t npts,
                             float **out_vals) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    *out_vals = (float *)malloc(npts * sizeof(float));
    if (!*out_vals) {
        tvdb_dense_grid_free(&g);
        snprintf(s_error_msg, sizeof(s_error_msg), "sample_quadratic: malloc failed");
        return -1;
    }
    tvdb_sample_quadratic_dense_batch(&g, (const tvdb_vec3f *)points, npts, *out_vals);
    tvdb_dense_grid_free(&g);
    return 0;
}

// Update an existing pair of (tsdf, weights) DenseGrid buffers with a new
// depth frame. Caller-provided buffers must already be initialized
// (typically tsdf = trunc_distance, weights = 0 on the first call).
int tvdb_py_integrate_tsdf_into(float *tsdf_data, float *wgt_data,
                                int nx, int ny, int nz, float voxel_size,
                                float ox, float oy, float oz,
                                const float *depth, int W, int H,
                                float fx, float fy, float cx_, float cy_,
                                const float *pose_wc /* 12 */,
                                float trunc_distance, float dmin, float dmax) {
    tvdb_dense_grid tsdf, wgt;
    tsdf.nx = wgt.nx = nx; tsdf.ny = wgt.ny = ny; tsdf.nz = wgt.nz = nz;
    tsdf.voxel_size = wgt.voxel_size = voxel_size;
    tsdf.ox = wgt.ox = ox; tsdf.oy = wgt.oy = oy; tsdf.oz = wgt.oz = oz;
    tsdf.data = tsdf_data; wgt.data = wgt_data;

    tvdb_depth_frame fr;
    fr.width = W; fr.height = H; fr.depth = depth;
    fr.fx = fx; fr.fy = fy; fr.cx = cx_; fr.cy = cy_;
    memcpy(fr.pose, pose_wc, 12 * sizeof(float));
    fr.trunc_distance = trunc_distance;
    fr.depth_min = dmin; fr.depth_max = dmax;

    return tvdb_integrate_tsdf(&tsdf, &wgt, &fr) ? 0 : -1;
}

// Same but also fuses RGB into a 3-channel color buffer.
int tvdb_py_integrate_tsdf_with_color_into(float *tsdf_data, float *wgt_data,
                                           float *col_data,
                                           int nx, int ny, int nz, float voxel_size,
                                           float ox, float oy, float oz,
                                           const float *depth, int W, int H,
                                           float fx, float fy, float cx_, float cy_,
                                           const float *pose_wc, float trunc_distance,
                                           float dmin, float dmax,
                                           const uint8_t *rgb) {
    tvdb_dense_grid tsdf, wgt;
    tsdf.nx = wgt.nx = nx; tsdf.ny = wgt.ny = ny; tsdf.nz = wgt.nz = nz;
    tsdf.voxel_size = wgt.voxel_size = voxel_size;
    tsdf.ox = wgt.ox = ox; tsdf.oy = wgt.oy = oy; tsdf.oz = wgt.oz = oz;
    tsdf.data = tsdf_data; wgt.data = wgt_data;

    tvdb_dense_vec_grid col;
    col.nx = nx; col.ny = ny; col.nz = nz;
    col.voxel_size = voxel_size;
    col.ox = ox; col.oy = oy; col.oz = oz;
    col.data = col_data;

    tvdb_depth_frame fr;
    fr.width = W; fr.height = H; fr.depth = depth;
    fr.fx = fx; fr.fy = fy; fr.cx = cx_; fr.cy = cy_;
    memcpy(fr.pose, pose_wc, 12 * sizeof(float));
    fr.trunc_distance = trunc_distance;
    fr.depth_min = dmin; fr.depth_max = dmax;

    return tvdb_integrate_tsdf_with_color(&tsdf, &wgt, &col, &fr, rgb) ? 0 : -1;
}

int tvdb_py_integrate_tsdf(const float *depth, int W, int H,
                           float fx, float fy, float cx_, float cy_,
                           const float *pose_wc /* 12 */,
                           float trunc_distance, float dmin, float dmax,
                           int nx, int ny, int nz, float voxel_size,
                           float ox, float oy, float oz,
                           float **out_tsdf, float **out_weights) {
    tvdb_dense_grid tsdf, wgt;
    tvdb_dense_grid_init(&tsdf, nx, ny, nz);
    tsdf.voxel_size = voxel_size; tsdf.ox = ox; tsdf.oy = oy; tsdf.oz = oz;
    tvdb_dense_grid_init(&wgt, nx, ny, nz);
    wgt.voxel_size = voxel_size; wgt.ox = ox; wgt.oy = oy; wgt.oz = oz;
    size_t total = (size_t)nx * ny * nz;
    for (size_t i = 0; i < total; ++i) tsdf.data[i] = trunc_distance;

    tvdb_depth_frame fr;
    fr.width = W; fr.height = H; fr.depth = depth;
    fr.fx = fx; fr.fy = fy; fr.cx = cx_; fr.cy = cy_;
    memcpy(fr.pose, pose_wc, 12 * sizeof(float));
    fr.trunc_distance = trunc_distance;
    fr.depth_min = dmin; fr.depth_max = dmax;

    bool ok = tvdb_integrate_tsdf(&tsdf, &wgt, &fr);
    if (!ok) {
        tvdb_dense_grid_free(&tsdf); tvdb_dense_grid_free(&wgt);
        snprintf(s_error_msg, sizeof(s_error_msg), "integrate_tsdf failed");
        return -1;
    }
    *out_tsdf    = (float *)malloc(total * sizeof(float));
    *out_weights = (float *)malloc(total * sizeof(float));
    if (!*out_tsdf || !*out_weights) {
        free(*out_tsdf); free(*out_weights);
        tvdb_dense_grid_free(&tsdf); tvdb_dense_grid_free(&wgt);
        return -1;
    }
    memcpy(*out_tsdf,    tsdf.data, total * sizeof(float));
    memcpy(*out_weights, wgt.data,  total * sizeof(float));
    tvdb_dense_grid_free(&tsdf); tvdb_dense_grid_free(&wgt);
    return 0;
}

#define RUN_RESIZE(FN)                                                        \
    tvdb_dense_grid in = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz); \
    tvdb_dense_grid out;                                                      \
    tvdb_dense_grid_init(&out, 0, 0, 0);                                      \
    bool _ok = FN(&in, factor, &out, NULL);                                   \
    if (!_ok) {                                                               \
        tvdb_dense_grid_free(&in); tvdb_dense_grid_free(&out);                \
        snprintf(s_error_msg, sizeof(s_error_msg), #FN " failed");            \
        return -1;                                                            \
    }                                                                         \
    *out_nx = out.nx; *out_ny = out.ny; *out_nz = out.nz;                     \
    *out_vs = out.voxel_size;                                                 \
    *out_ox_ = out.ox; *out_oy_ = out.oy; *out_oz_ = out.oz;                  \
    size_t _N = (size_t)out.nx * out.ny * out.nz;                             \
    *out_data = (float *)malloc(_N * sizeof(float));                          \
    if (*out_data) memcpy(*out_data, out.data, _N * sizeof(float));           \
    tvdb_dense_grid_free(&in); tvdb_dense_grid_free(&out);                    \
    return *out_data ? 0 : -1

int tvdb_py_coarsen_grid(const float *data, int nx, int ny, int nz,
                         float voxel_size, float ox, float oy, float oz,
                         int factor,
                         float **out_data, int *out_nx, int *out_ny, int *out_nz,
                         float *out_vs, float *out_ox_, float *out_oy_, float *out_oz_) {
    RUN_RESIZE(tvdb_coarsen_grid);
}
int tvdb_py_refine_grid(const float *data, int nx, int ny, int nz,
                        float voxel_size, float ox, float oy, float oz,
                        int factor,
                        float **out_data, int *out_nx, int *out_ny, int *out_nz,
                        float *out_vs, float *out_ox_, float *out_oy_, float *out_oz_) {
    RUN_RESIZE(tvdb_refine_grid);
}

int tvdb_py_resample_grid(const float *data, int nx, int ny, int nz,
                          float voxel_size, float ox, float oy, float oz,
                          float new_voxel_size, int order,
                          float **out_data, int *out_nx, int *out_ny, int *out_nz,
                          float *out_vs, float *out_ox_, float *out_oy_, float *out_oz_) {
    tvdb_dense_grid in = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_grid out; tvdb_dense_grid_init(&out, 0, 0, 0);
    if (!tvdb_resample_grid(&in, new_voxel_size, order, &out, NULL)) {
        tvdb_dense_grid_free(&in); tvdb_dense_grid_free(&out);
        snprintf(s_error_msg, sizeof(s_error_msg), "resample_grid failed");
        return -1;
    }
    *out_nx = out.nx; *out_ny = out.ny; *out_nz = out.nz;
    *out_vs = out.voxel_size; *out_ox_ = out.ox; *out_oy_ = out.oy; *out_oz_ = out.oz;
    size_t N = (size_t)out.nx * out.ny * out.nz;
    *out_data = (float *)malloc(N * sizeof(float));
    if (*out_data) memcpy(*out_data, out.data, N * sizeof(float));
    tvdb_dense_grid_free(&in); tvdb_dense_grid_free(&out);
    return *out_data ? 0 : -1;
}
#undef RUN_RESIZE

#define RUN_POOL(FN)                                                          \
    tvdb_dense_grid in = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz); \
    tvdb_dense_grid out;                                                      \
    tvdb_dense_grid_init(&out, 0, 0, 0);                                      \
    FN(&in, kx, ky, kz, &out, NULL);                                          \
    *out_nx = out.nx; *out_ny = out.ny; *out_nz = out.nz;                     \
    *out_vs = out.voxel_size;                                                 \
    *out_ox_ = out.ox; *out_oy_ = out.oy; *out_oz_ = out.oz;                  \
    size_t _N = (size_t)out.nx * out.ny * out.nz;                             \
    *out_data = (float *)malloc(_N * sizeof(float));                          \
    if (*out_data) memcpy(*out_data, out.data, _N * sizeof(float));           \
    tvdb_dense_grid_free(&in); tvdb_dense_grid_free(&out);                    \
    return *out_data ? 0 : -1

int tvdb_py_max_pool(const float *data, int nx, int ny, int nz,
                     float voxel_size, float ox, float oy, float oz,
                     int kx, int ky, int kz,
                     float **out_data, int *out_nx, int *out_ny, int *out_nz,
                     float *out_vs, float *out_ox_, float *out_oy_, float *out_oz_) {
    RUN_POOL(tvdb_max_pool);
}
int tvdb_py_avg_pool(const float *data, int nx, int ny, int nz,
                     float voxel_size, float ox, float oy, float oz,
                     int kx, int ky, int kz,
                     float **out_data, int *out_nx, int *out_ny, int *out_nz,
                     float *out_vs, float *out_ox_, float *out_oy_, float *out_oz_) {
    RUN_POOL(tvdb_avg_pool);
}
#undef RUN_POOL

/* ======================================================================== */
/*  Splat / ray ops / clip / prune / merge                                   */
/* ======================================================================== */

int tvdb_py_splat_trilinear(float *data, int nx, int ny, int nz,
                            float voxel_size, float ox, float oy, float oz,
                            const float *pts, const float *vals, size_t npts,
                            float *weights /* may be NULL */) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_splat_trilinear_dense(&g, (const tvdb_vec3f *)pts, vals, npts, weights);
    memcpy(data, g.data, (size_t)nx * ny * nz * sizeof(float));
    tvdb_dense_grid_free(&g);
    return 0;
}

int tvdb_py_voxels_along_ray(const float *data, int nx, int ny, int nz,
                             float voxel_size, float ox, float oy, float oz,
                             float rx, float ry, float rz,
                             float dx, float dy, float dz,
                             float tmin, float tmax,
                             int **out_voxels /* xyz triples */, size_t *out_count) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ray ray;
    ray.origin.x = rx; ray.origin.y = ry; ray.origin.z = rz;
    ray.dir.x = dx;    ray.dir.y = dy;    ray.dir.z = dz;
    ray.tmin = tmin;   ray.tmax = tmax;
    size_t cnt = tvdb_voxels_along_ray_dense(&g, &ray, NULL, 0);
    *out_count = cnt;
    if (cnt == 0) {
        *out_voxels = NULL;
        tvdb_dense_grid_free(&g);
        return 0;
    }
    tvdb_vec3i *buf = (tvdb_vec3i *)malloc(cnt * sizeof(tvdb_vec3i));
    if (!buf) { tvdb_dense_grid_free(&g); return -1; }
    tvdb_voxels_along_ray_dense(&g, &ray, buf, cnt);
    *out_voxels = (int *)buf;  // 3 ints per voxel: layout matches tvdb_vec3i
    tvdb_dense_grid_free(&g);
    return 0;
}

int tvdb_py_uniform_ray_samples(float rx, float ry, float rz,
                                float dx, float dy, float dz,
                                float tmin, float tmax, size_t n,
                                float **out_points /* xyz triples */,
                                float **out_t) {
    tvdb_ray ray;
    ray.origin.x = rx; ray.origin.y = ry; ray.origin.z = rz;
    ray.dir.x = dx;    ray.dir.y = dy;    ray.dir.z = dz;
    ray.tmin = tmin;   ray.tmax = tmax;
    *out_points = (float *)malloc(n * 3 * sizeof(float));
    *out_t      = (float *)malloc(n * sizeof(float));
    if (!*out_points || !*out_t) {
        free(*out_points); free(*out_t);
        return -1;
    }
    tvdb_uniform_ray_samples(&ray, n, (tvdb_vec3f *)*out_points, *out_t);
    return 0;
}

int tvdb_py_segments_along_ray(const float *data, int nx, int ny, int nz,
                               float voxel_size, float ox, float oy, float oz,
                               float rx, float ry, float rz,
                               float dx, float dy, float dz,
                               float tmin, float tmax, float isovalue,
                               size_t step_count, size_t cap,
                               float **out_pairs, size_t *out_count) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ray ray;
    ray.origin.x = rx; ray.origin.y = ry; ray.origin.z = rz;
    ray.dir.x = dx;    ray.dir.y = dy;    ray.dir.z = dz;
    ray.tmin = tmin;   ray.tmax = tmax;
    *out_pairs = (float *)malloc(cap * 2 * sizeof(float));
    if (!*out_pairs) { tvdb_dense_grid_free(&g); return -1; }
    *out_count = tvdb_segments_along_ray(&g, &ray, isovalue, step_count, *out_pairs, cap);
    tvdb_dense_grid_free(&g);
    return 0;
}

int tvdb_py_clip_grid(const float *data, int nx, int ny, int nz,
                      float voxel_size, float ox, float oy, float oz,
                      const float bbox_min[3], const float bbox_max[3],
                      float **out_data, int *out_nx, int *out_ny, int *out_nz,
                      float *out_vs, float *out_ox_, float *out_oy_, float *out_oz_) {
    tvdb_dense_grid in = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_dense_grid out;
    tvdb_dense_grid_init(&out, 0, 0, 0);
    bool ok = tvdb_clip_grid(&in, bbox_min, bbox_max, &out, NULL);
    if (!ok) {
        tvdb_dense_grid_free(&in); tvdb_dense_grid_free(&out);
        snprintf(s_error_msg, sizeof(s_error_msg), "clip_grid: empty intersection");
        return -1;
    }
    *out_nx = out.nx; *out_ny = out.ny; *out_nz = out.nz;
    *out_vs = out.voxel_size;
    *out_ox_ = out.ox; *out_oy_ = out.oy; *out_oz_ = out.oz;
    size_t N = (size_t)out.nx * out.ny * out.nz;
    *out_data = (float *)malloc(N * sizeof(float));
    if (*out_data) memcpy(*out_data, out.data, N * sizeof(float));
    tvdb_dense_grid_free(&in); tvdb_dense_grid_free(&out);
    return *out_data ? 0 : -1;
}

int tvdb_py_prune_grid(float *data, int nx, int ny, int nz,
                       float voxel_size, float ox, float oy, float oz,
                       float background, float tolerance) {
    tvdb_dense_grid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_prune_grid(&g, background, tolerance);
    memcpy(data, g.data, (size_t)nx * ny * nz * sizeof(float));
    tvdb_dense_grid_free(&g);
    return 0;
}

/* ======================================================================== */
/*  Bridge: ops on tvdb_grid_t* (loaded VDB grids)                            */
/* ======================================================================== */

size_t tvdb_py_grid_active_voxel_count(const tvdb_grid_t *grid) {
    return tvdb_grid_active_voxel_count(grid);
}

int tvdb_py_grid_active_bbox(const tvdb_grid_t *grid,
                             int32_t out_min[3], int32_t out_max[3]) {
    return tvdb_grid_active_bbox(grid, out_min, out_max) ? 0 : -1;
}

float tvdb_py_grid_float_background(const tvdb_grid_t *grid) {
    return tvdb_grid_float_background(grid);
}

int tvdb_py_grid_materialize_dense(const tvdb_grid_t *grid,
                                   const int32_t bbox_min[3],
                                   const int32_t bbox_max[3],
                                   float background,
                                   float **out_data, int *nx, int *ny, int *nz,
                                   float *out_vs, float *out_ox,
                                   float *out_oy, float *out_oz) {
    tvdb_dense_grid g;
    if (!tvdb_grid_materialize_dense(grid, bbox_min, bbox_max, background, &g)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "materialize_dense failed");
        return -1;
    }
    *nx = g.nx; *ny = g.ny; *nz = g.nz;
    *out_vs = g.voxel_size;
    *out_ox = g.ox; *out_oy = g.oy; *out_oz = g.oz;
    size_t N = (size_t)g.nx * g.ny * g.nz;
    *out_data = (float *)malloc(N * sizeof(float));
    if (*out_data) memcpy(*out_data, g.data, N * sizeof(float));
    tvdb_dense_grid_free(&g);
    return *out_data ? 0 : -1;
}

// Dilate / erode active. Returns concat'd buffers: out_coords as int32[count*3],
// out_values as float[count].
static int grid_morph_active_impl(const tvdb_grid_t *grid, int iterations,
                                  bool dilate,
                                  int32_t **out_coords, float **out_values,
                                  size_t *out_count) {
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    bool ok = dilate ? tvdb_grid_dilate_active(grid, iterations, &sg)
                     : tvdb_grid_erode_active(grid, iterations, &sg);
    if (!ok) {
        tvdb_sparse_grid_free(&sg);
        snprintf(s_error_msg, sizeof(s_error_msg),
                 dilate ? "grid_dilate_active failed" : "grid_erode_active failed");
        return -1;
    }
    *out_count = sg.count;
    if (sg.count == 0) {
        *out_coords = NULL; *out_values = NULL;
        tvdb_sparse_grid_free(&sg);
        return 0;
    }
    *out_coords = (int32_t *)malloc(sg.count * 3 * sizeof(int32_t));
    *out_values = (float *)malloc(sg.count * sizeof(float));
    if (!*out_coords || !*out_values) {
        free(*out_coords); free(*out_values);
        tvdb_sparse_grid_free(&sg);
        return -1;
    }
    for (size_t i = 0; i < sg.count; ++i) {
        (*out_coords)[3*i + 0] = sg.coords[i].x;
        (*out_coords)[3*i + 1] = sg.coords[i].y;
        (*out_coords)[3*i + 2] = sg.coords[i].z;
    }
    memcpy(*out_values, sg.values, sg.count * sizeof(float));
    tvdb_sparse_grid_free(&sg);
    return 0;
}

int tvdb_py_grid_dilate_active(const tvdb_grid_t *grid, int iterations,
                               int32_t **out_coords, float **out_values,
                               size_t *out_count) {
    return grid_morph_active_impl(grid, iterations, true,
                                  out_coords, out_values, out_count);
}
int tvdb_py_grid_erode_active(const tvdb_grid_t *grid, int iterations,
                              int32_t **out_coords, float **out_values,
                              size_t *out_count) {
    return grid_morph_active_impl(grid, iterations, false,
                                  out_coords, out_values, out_count);
}

// Topology-growing/shrinking morph: dispatch on `grow` flag.
static int grid_morph_topology_impl(const tvdb_grid_t *grid, int iterations, int grow,
                                    int32_t **out_coords, float **out_values,
                                    size_t *out_count) {
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    bool ok = grow ? tvdb_grid_dilate_topology(grid, iterations, &sg)
                   : tvdb_grid_erode_topology(grid, iterations, &sg);
    if (!ok) {
        tvdb_sparse_grid_free(&sg);
        snprintf(s_error_msg, sizeof(s_error_msg),
                 grow ? "grid_dilate_topology failed" : "grid_erode_topology failed");
        return -1;
    }
    *out_count = sg.count;
    if (sg.count == 0) {
        *out_coords = NULL; *out_values = NULL;
        tvdb_sparse_grid_free(&sg);
        return 0;
    }
    *out_coords = (int32_t *)malloc(sg.count * 3 * sizeof(int32_t));
    *out_values = (float *)malloc(sg.count * sizeof(float));
    if (!*out_coords || !*out_values) {
        free(*out_coords); free(*out_values);
        tvdb_sparse_grid_free(&sg);
        return -1;
    }
    for (size_t i = 0; i < sg.count; ++i) {
        (*out_coords)[3*i + 0] = sg.coords[i].x;
        (*out_coords)[3*i + 1] = sg.coords[i].y;
        (*out_coords)[3*i + 2] = sg.coords[i].z;
    }
    memcpy(*out_values, sg.values, sg.count * sizeof(float));
    tvdb_sparse_grid_free(&sg);
    return 0;
}

int tvdb_py_grid_dilate_topology(const tvdb_grid_t *grid, int iterations,
                                 int32_t **out_coords, float **out_values,
                                 size_t *out_count) {
    return grid_morph_topology_impl(grid, iterations, /*grow=*/1,
                                    out_coords, out_values, out_count);
}
int tvdb_py_grid_erode_topology(const tvdb_grid_t *grid, int iterations,
                                int32_t **out_coords, float **out_values,
                                size_t *out_count) {
    return grid_morph_topology_impl(grid, iterations, /*grow=*/0,
                                    out_coords, out_values, out_count);
}

// Multi-channel sparse 3D convolution.
// Output: out_coords[count*3], out_values[count * c_out].
int tvdb_py_sparse_conv3d_mc(const int32_t *in_coords, const float *in_values_mc, size_t in_count,
                             int c_in, float voxel_size, float ox, float oy, float oz,
                             const float *kernel, int kx, int ky, int kz, int c_out,
                             float pad_value,
                             int32_t **out_coords, float **out_values_mc, size_t *out_count) {
    tvdb_sparse_grid in; tvdb_sparse_grid_init(&in);
    if (in_count > 0) {
        if (!tvdb_sparse_grid_reserve(&in, in_count)) {
            snprintf(s_error_msg, sizeof(s_error_msg), "conv3d_mc: alloc failed");
            return -1;
        }
        for (size_t i = 0; i < in_count; ++i) {
            in.coords[i].x = in_coords[3*i + 0];
            in.coords[i].y = in_coords[3*i + 1];
            in.coords[i].z = in_coords[3*i + 2];
        }
        in.count = in_count;
        in.voxel_size = voxel_size; in.ox = ox; in.oy = oy; in.oz = oz;
    }
    tvdb_sparse_grid out; tvdb_sparse_grid_init(&out);
    float *out_mc = NULL;
    if (!tvdb_sparse_conv3d_mc(&in, in_values_mc, c_in, kernel, kx, ky, kz, c_out,
                                pad_value, &out, &out_mc)) {
        tvdb_sparse_grid_free(&in);
        tvdb_sparse_grid_free(&out);
        free(out_mc);
        snprintf(s_error_msg, sizeof(s_error_msg), "sparse_conv3d_mc failed");
        return -1;
    }
    tvdb_sparse_grid_free(&in);
    *out_count = out.count;
    if (out.count == 0) {
        *out_coords = NULL; *out_values_mc = NULL;
        free(out_mc);
        tvdb_sparse_grid_free(&out);
        return 0;
    }
    *out_coords = (int32_t *)malloc(out.count * 3 * sizeof(int32_t));
    if (!*out_coords) {
        free(out_mc);
        tvdb_sparse_grid_free(&out);
        return -1;
    }
    for (size_t i = 0; i < out.count; ++i) {
        (*out_coords)[3*i + 0] = out.coords[i].x;
        (*out_coords)[3*i + 1] = out.coords[i].y;
        (*out_coords)[3*i + 2] = out.coords[i].z;
    }
    *out_values_mc = out_mc;  // ownership transfers
    tvdb_sparse_grid_free(&out);
    return 0;
}

// Sparse 3D convolution. Inputs as flat coord/value arrays; kernel kx*ky*kz floats.
int tvdb_py_sparse_conv3d(const int32_t *in_coords, const float *in_values, size_t in_count,
                          float voxel_size, float ox, float oy, float oz,
                          const float *kernel, int kx, int ky, int kz, float pad_value,
                          int32_t **out_coords, float **out_values, size_t *out_count) {
    tvdb_sparse_grid in; tvdb_sparse_grid_init(&in);
    if (in_count > 0) {
        if (!tvdb_sparse_grid_reserve(&in, in_count)) {
            snprintf(s_error_msg, sizeof(s_error_msg), "conv3d: alloc failed");
            return -1;
        }
        for (size_t i = 0; i < in_count; ++i) {
            in.coords[i].x = in_coords[3*i + 0];
            in.coords[i].y = in_coords[3*i + 1];
            in.coords[i].z = in_coords[3*i + 2];
            in.values[i] = in_values[i];
        }
        in.count = in_count;
        in.voxel_size = voxel_size; in.ox = ox; in.oy = oy; in.oz = oz;
    }
    tvdb_sparse_grid out; tvdb_sparse_grid_init(&out);
    if (!tvdb_sparse_conv3d(&in, kernel, kx, ky, kz, pad_value, &out)) {
        tvdb_sparse_grid_free(&in);
        tvdb_sparse_grid_free(&out);
        snprintf(s_error_msg, sizeof(s_error_msg), "sparse_conv3d failed");
        return -1;
    }
    tvdb_sparse_grid_free(&in);
    *out_count = out.count;
    if (out.count == 0) {
        *out_coords = NULL; *out_values = NULL;
        tvdb_sparse_grid_free(&out);
        return 0;
    }
    *out_coords = (int32_t *)malloc(out.count * 3 * sizeof(int32_t));
    *out_values = (float *)malloc(out.count * sizeof(float));
    if (!*out_coords || !*out_values) {
        free(*out_coords); free(*out_values);
        tvdb_sparse_grid_free(&out);
        return -1;
    }
    for (size_t i = 0; i < out.count; ++i) {
        (*out_coords)[3*i + 0] = out.coords[i].x;
        (*out_coords)[3*i + 1] = out.coords[i].y;
        (*out_coords)[3*i + 2] = out.coords[i].z;
    }
    memcpy(*out_values, out.values, out.count * sizeof(float));
    tvdb_sparse_grid_free(&out);
    return 0;
}

// Replace a file's grid at index `grid_idx` with a freshly-built grid from
// sparse coords/values, using the existing grid as a template (descriptor +
// transform + tree layout). The original grid contents are freed.
int tvdb_py_replace_grid_from_sparse(tvdb_file_t *file, size_t grid_idx,
                                     const int32_t *coords, const float *values, size_t count,
                                     const char *new_name, float background) {
    if (!file || grid_idx >= file->num_grids) {
        snprintf(s_error_msg, sizeof(s_error_msg), "replace_grid_from_sparse: bad grid_idx");
        return -1;
    }
    tvdb_grid_t *tmpl = &file->grids[grid_idx];

    // Build a sparse_grid from the inputs.
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    if (count > 0) {
        if (!tvdb_sparse_grid_reserve(&sg, count)) {
            snprintf(s_error_msg, sizeof(s_error_msg), "alloc failed");
            return -1;
        }
        for (size_t i = 0; i < count; ++i) {
            sg.coords[i].x = coords[3*i + 0];
            sg.coords[i].y = coords[3*i + 1];
            sg.coords[i].z = coords[3*i + 2];
            sg.values[i] = values[i];
        }
        sg.count = count;
    }

    // Build the new grid.
    tvdb_grid_t built;
    if (!tvdb_grid_from_sparse_using_template(tmpl, &sg, new_name, background, &built)) {
        tvdb_sparse_grid_free(&sg);
        snprintf(s_error_msg, sizeof(s_error_msg), "grid_from_sparse_using_template failed");
        return -1;
    }
    tvdb_sparse_grid_free(&sg);

    // Free the template-grid's old contents and overwrite with the new grid.
    // We use tvdb_grid_destroy_owned which only works if the grid was built by
    // us; for loader-allocated grids we rely on tvdb_file_close to clean up.
    // Here we trust that the file's allocator is the system default (malloc-
    // backed) — true when tvdb_file_open was called with NULL allocator.
    // Manually reset the destination's allocator pointers to ours so the
    // file_close path is consistent.
    tvdb_grid_destroy_owned(tmpl);
    *tmpl = built;
    return 0;
}

/* System (malloc-backed) allocator. The io implementation's own default
   allocator is file-local to tinyvdb_io.c, so we provide one here for building
   a tvdb_file_t from scratch (no template file to inherit an allocator from). */
static void *tvdb_py__sys_malloc(size_t size, void *ctx) { (void)ctx; return malloc(size); }
static void *tvdb_py__sys_realloc(void *ptr, size_t oldsz, size_t newsz, void *ctx) {
    (void)ctx; (void)oldsz; return realloc(ptr, newsz);
}
static void tvdb_py__sys_free(void *ptr, size_t size, void *ctx) { (void)ctx; (void)size; free(ptr); }
static tvdb_allocator_t tvdb_py__sys_allocator(void) {
    tvdb_allocator_t a;
    a.malloc_fn = tvdb_py__sys_malloc;
    a.realloc_fn = tvdb_py__sys_realloc;
    a.free_fn = tvdb_py__sys_free;
    a.user_ctx = NULL;
    return a;
}

/* OpenVDB grid-type string for a scalar/vector value type (Tree_*_5_4_3). The
   generic builder also derives this internally, but setting it on the template
   keeps the synthesized template self-consistent. */
static const char *tvdb_py__grid_type_str(tvdb_value_type_t vt) {
    switch (vt) {
        case TVDB_VALUE_FLOAT:  return "Tree_float_5_4_3";
        case TVDB_VALUE_DOUBLE: return "Tree_double_5_4_3";
        case TVDB_VALUE_INT32:  return "Tree_int32_5_4_3";
        case TVDB_VALUE_INT64:  return "Tree_int64_5_4_3";
        case TVDB_VALUE_BOOL:   return "Tree_bool_5_4_3";
        case TVDB_VALUE_VEC3F:  return "Tree_vec3s_5_4_3";
        case TVDB_VALUE_VEC3D:  return "Tree_vec3d_5_4_3";
        case TVDB_VALUE_VEC3I:  return "Tree_vec3i_5_4_3";
        default:                return "Tree_float_5_4_3";
    }
}

/* Shared core: synthesize a Tree_<type>_5_4_3 template (layout + per-axis
   ScaleTranslateMap transform), build the grid tree from (coords, values), and
   save it as a one-grid .vdb file. `coords` are world-voxel indices; the
   transform maps world = voxel_size * index + origin. `bg_bytes` is one element
   worth of background fill. Returns 0 on success, -1 on error. */
static int tvdb_py__build_save_typed(const char *path,
                                     const tvdb_vec3i *coords, const void *values,
                                     size_t count, tvdb_value_type_t vt,
                                     double vsx, double vsy, double vsz,
                                     double ox, double oy, double oz,
                                     const char *grid_name, const void *bg_bytes,
                                     uint32_t compression, int level) {
    /* 1) Synthetic template (Tree_<type>_5_4_3) carrying only the layout, grid
          type and transform — its (empty) tree is unused by the builder. */
    tvdb_grid_t tmpl;
    memset(&tmpl, 0, sizeof(tmpl));
    char grid_type[32];
    snprintf(grid_type, sizeof(grid_type), "%s", tvdb_py__grid_type_str(vt));
    tmpl.descriptor.grid_type = grid_type;  /* builder duplicates this string */
    tmpl.tree.layout.num_levels = 4;
    tmpl.tree.layout.levels[0].node_type = TVDB_NODE_ROOT;
    tmpl.tree.layout.levels[1].node_type = TVDB_NODE_INTERNAL;
    tmpl.tree.layout.levels[2].node_type = TVDB_NODE_INTERNAL;
    tmpl.tree.layout.levels[3].node_type = TVDB_NODE_LEAF;
    tmpl.tree.layout.levels[0].log2dim = 0;
    tmpl.tree.layout.levels[1].log2dim = 5;
    tmpl.tree.layout.levels[2].log2dim = 4;
    tmpl.tree.layout.levels[3].log2dim = 3;
    for (int lv = 0; lv < 4; ++lv) tmpl.tree.layout.levels[lv].value_type = vt;
    tmpl.transform.type = TVDB_TRANSFORM_SCALE_TRANSLATE;
    tmpl.transform.scale_values[0] = vsx; tmpl.transform.scale_values[1] = vsy; tmpl.transform.scale_values[2] = vsz;
    tmpl.transform.voxel_size[0] = vsx;   tmpl.transform.voxel_size[1] = vsy;   tmpl.transform.voxel_size[2] = vsz;
    tmpl.transform.translation[0] = ox;   tmpl.transform.translation[1] = oy;   tmpl.transform.translation[2] = oz;

    /* 2) Build the grid tree from the (coord, value) pairs. */
    tvdb_grid_t built;
    bool ok = tvdb_grid_from_sparse_typed_using_template(&tmpl, coords, values, count,
                                                         vt, bg_bytes,
                                                         grid_name ? grid_name : "grid", &built);
    if (!ok) {
        snprintf(s_error_msg, sizeof(s_error_msg), "write_grid: grid build failed");
        return -1;
    }

    /* 3) Assemble a one-grid file (zeroed header -> writer defaults to v224) and save. */
    tvdb_file_t out;
    memset(&out, 0, sizeof(out));
    out.alloc = tvdb_py__sys_allocator();
    out.num_grids = 1;
    out.grids = &built;
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));
    tvdb_status_t st = tvdb_file_save(&out, path, compression, level, /*use_mmap=*/0, &err);
    tvdb_grid_destroy_owned(&built);
    if (st != TVDB_OK) {
        snprintf(s_error_msg, sizeof(s_error_msg), "write_grid: save failed: %s",
                 err.message[0] ? err.message : "unknown");
        return -1;
    }
    return 0;
}

/* Write a dense grid of arbitrary value type (e.g. an SDF / level set, an int
   label field, or a vec3 velocity field) to a .vdb file from scratch. `values`
   holds `count` elements (= nx*ny*nz voxels), each tvdb_value_type_size(vt)
   bytes wide, in C order: index = (i*ny + j)*nz + k for voxel (i,j,k). The grid
   uses a per-axis ScaleTranslateMap so that world = voxel_size * index + origin.
   `bg_bytes` is one element worth of background fill (inactive voxels / tiles).
   Returns 0 on success, -1 on error. */
int tvdb_py_write_grid_dense_typed(const char *path,
                                   const void *values, size_t count,
                                   int value_type,
                                   int nx, int ny, int nz,
                                   double vsx, double vsy, double vsz,
                                   double ox, double oy, double oz,
                                   const char *grid_name, const void *bg_bytes,
                                   uint32_t compression, int level) {
    if (!path || !values || !bg_bytes) {
        snprintf(s_error_msg, sizeof(s_error_msg), "write_grid_dense: NULL argument");
        return -1;
    }
    tvdb_value_type_t vt = (tvdb_value_type_t)value_type;
    if (nx <= 0 || ny <= 0 || nz <= 0 ||
        (size_t)nx * (size_t)ny * (size_t)nz != count) {
        snprintf(s_error_msg, sizeof(s_error_msg),
                 "write_grid_dense: nx*ny*nz (%lld) != value count (%zu)",
                 (long long)nx * ny * nz, count);
        return -1;
    }

    /* Dense -> sparse: one active voxel per cell at integer coords (0..n-1). */
    tvdb_vec3i *coords = (tvdb_vec3i *)malloc(count * sizeof(tvdb_vec3i));
    if (!coords) {
        snprintf(s_error_msg, sizeof(s_error_msg), "write_grid_dense: alloc failed");
        return -1;
    }
    size_t idx = 0;
    for (int i = 0; i < nx; ++i)
        for (int j = 0; j < ny; ++j)
            for (int k = 0; k < nz; ++k) {
                coords[idx].x = i; coords[idx].y = j; coords[idx].z = k; ++idx;
            }

    int rc = tvdb_py__build_save_typed(path, coords, values, count, vt,
                                       vsx, vsy, vsz, ox, oy, oz,
                                       grid_name ? grid_name : "sdf", bg_bytes,
                                       compression, level);
    free(coords);
    return rc;
}

/* Write a sparse grid of arbitrary value type from scratch. `coords` is
   `count` world-voxel index triples (int32 x,y,z); `values` is `count` elements
   each tvdb_value_type_size(vt) bytes wide, paired with `coords` by position.
   Same transform / background semantics as the dense writer. Coordinates that
   collide are resolved by the builder (last writer wins per the builder's leaf
   grouping). Returns 0 on success, -1 on error. */
int tvdb_py_write_grid_sparse_typed(const char *path,
                                    const int32_t *coords, const void *values,
                                    size_t count, int value_type,
                                    double vsx, double vsy, double vsz,
                                    double ox, double oy, double oz,
                                    const char *grid_name, const void *bg_bytes,
                                    uint32_t compression, int level) {
    if (!path || !bg_bytes || (count > 0 && (!coords || !values))) {
        snprintf(s_error_msg, sizeof(s_error_msg), "write_grid_sparse: NULL argument");
        return -1;
    }
    tvdb_value_type_t vt = (tvdb_value_type_t)value_type;

    /* Repack int32 triples into tvdb_vec3i (same layout, but be explicit). */
    tvdb_vec3i *cv = NULL;
    if (count > 0) {
        cv = (tvdb_vec3i *)malloc(count * sizeof(tvdb_vec3i));
        if (!cv) {
            snprintf(s_error_msg, sizeof(s_error_msg), "write_grid_sparse: alloc failed");
            return -1;
        }
        for (size_t i = 0; i < count; ++i) {
            cv[i].x = coords[3 * i + 0];
            cv[i].y = coords[3 * i + 1];
            cv[i].z = coords[3 * i + 2];
        }
    }
    int rc = tvdb_py__build_save_typed(path, cv, values, count, vt,
                                       vsx, vsy, vsz, ox, oy, oz,
                                       grid_name ? grid_name : "grid", bg_bytes,
                                       compression, level);
    free(cv);
    return rc;
}

/* Back-compat float entry point: packs the float background and delegates. */
int tvdb_py_write_float_grid_dense(const char *path,
                                   const float *values, size_t count,
                                   int nx, int ny, int nz,
                                   double vsx, double vsy, double vsz,
                                   double ox, double oy, double oz,
                                   const char *grid_name, float background,
                                   uint32_t compression, int level) {
    return tvdb_py_write_grid_dense_typed(path, values, count, TVDB_VALUE_FLOAT,
                                          nx, ny, nz, vsx, vsy, vsz, ox, oy, oz,
                                          grid_name, &background, compression, level);
}

// Sparse conv3d VJPs.
int tvdb_py_sparse_conv3d_vjp_values(const int32_t *in_coords, size_t in_count,
                                     const float *grad_out_values,
                                     const float *kernel, int kx, int ky, int kz,
                                     float **out_grad_in /* malloc'd, length in_count */) {
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    if (in_count > 0) {
        if (!tvdb_sparse_grid_reserve(&sg, in_count)) {
            snprintf(s_error_msg, sizeof(s_error_msg), "vjp_values: alloc failed");
            return -1;
        }
        for (size_t i = 0; i < in_count; ++i) {
            sg.coords[i].x = in_coords[3*i + 0];
            sg.coords[i].y = in_coords[3*i + 1];
            sg.coords[i].z = in_coords[3*i + 2];
        }
        sg.count = in_count;
    }
    *out_grad_in = (float *)calloc(in_count, sizeof(float));
    if (!*out_grad_in && in_count > 0) {
        tvdb_sparse_grid_free(&sg); return -1;
    }
    bool ok = tvdb_sparse_conv3d_vjp_values(&sg, grad_out_values, kernel,
                                            kx, ky, kz, *out_grad_in);
    tvdb_sparse_grid_free(&sg);
    if (!ok) {
        free(*out_grad_in); *out_grad_in = NULL;
        snprintf(s_error_msg, sizeof(s_error_msg), "sparse_conv3d_vjp_values failed");
        return -1;
    }
    return 0;
}

int tvdb_py_sparse_conv3d_vjp_kernel(const int32_t *in_coords, const float *in_values,
                                     size_t in_count,
                                     const float *grad_out_values,
                                     int kx, int ky, int kz,
                                     float **out_grad_kernel /* malloc'd, length kx*ky*kz */) {
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    if (in_count > 0) {
        if (!tvdb_sparse_grid_reserve(&sg, in_count)) {
            snprintf(s_error_msg, sizeof(s_error_msg), "vjp_kernel: alloc failed");
            return -1;
        }
        for (size_t i = 0; i < in_count; ++i) {
            sg.coords[i].x = in_coords[3*i + 0];
            sg.coords[i].y = in_coords[3*i + 1];
            sg.coords[i].z = in_coords[3*i + 2];
            sg.values[i] = in_values[i];
        }
        sg.count = in_count;
    }
    size_t klen = (size_t)kx * (size_t)ky * (size_t)kz;
    *out_grad_kernel = (float *)calloc(klen, sizeof(float));
    if (!*out_grad_kernel) {
        tvdb_sparse_grid_free(&sg); return -1;
    }
    bool ok = tvdb_sparse_conv3d_vjp_kernel(&sg, grad_out_values, kx, ky, kz,
                                            *out_grad_kernel);
    tvdb_sparse_grid_free(&sg);
    if (!ok) {
        free(*out_grad_kernel); *out_grad_kernel = NULL;
        snprintf(s_error_msg, sizeof(s_error_msg), "sparse_conv3d_vjp_kernel failed");
        return -1;
    }
    return 0;
}

// Topology-extending variant: rebuild the file's grid_idx-th grid as
// existing ∪ sparse (sparse wins on overlap). Useful when the sparse coords
// land outside any existing leaf — replace_grid_from_sparse drops those
// because it builds purely from the sparse input; this preserves the
// existing active set.
int tvdb_py_extend_grid_from_sparse(tvdb_file_t *file, size_t grid_idx,
                                    const int32_t *coords, const float *values, size_t count,
                                    const char *new_name, float background) {
    if (!file || grid_idx >= file->num_grids) {
        snprintf(s_error_msg, sizeof(s_error_msg), "extend_grid_from_sparse: bad grid_idx");
        return -1;
    }
    tvdb_grid_t *tmpl = &file->grids[grid_idx];

    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    if (count > 0) {
        if (!tvdb_sparse_grid_reserve(&sg, count)) {
            snprintf(s_error_msg, sizeof(s_error_msg), "alloc failed");
            return -1;
        }
        for (size_t i = 0; i < count; ++i) {
            sg.coords[i].x = coords[3*i + 0];
            sg.coords[i].y = coords[3*i + 1];
            sg.coords[i].z = coords[3*i + 2];
            sg.values[i] = values[i];
        }
        sg.count = count;
    }

    tvdb_grid_t built;
    bool ok = tvdb_grid_extend_from_sparse(tmpl, &sg, new_name, background, &built);
    tvdb_sparse_grid_free(&sg);
    if (!ok) {
        snprintf(s_error_msg, sizeof(s_error_msg), "grid_extend_from_sparse failed");
        return -1;
    }
    tvdb_grid_destroy_owned(tmpl);
    *tmpl = built;
    return 0;
}

// Update existing tree's voxel values from sparse coords/values
// (topology-preserving — coords outside any active leaf are skipped).
int tvdb_py_grid_update_from_sparse(tvdb_grid_t *grid,
                                    const int32_t *coords, const float *values,
                                    size_t count, size_t *out_updated,
                                    size_t *out_skipped) {
    if (!grid || (!coords && count) || (!values && count)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "update_from_sparse: bad args");
        return -1;
    }
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    if (count > 0 && !tvdb_sparse_grid_reserve(&sg, count)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "update_from_sparse: alloc failed");
        return -1;
    }
    sg.count = count;
    for (size_t i = 0; i < count; ++i) {
        sg.coords[i].x = coords[3*i + 0];
        sg.coords[i].y = coords[3*i + 1];
        sg.coords[i].z = coords[3*i + 2];
        sg.values[i] = values[i];
    }
    *out_updated = tvdb_grid_update_from_sparse(grid, &sg, out_skipped);
    tvdb_sparse_grid_free(&sg);
    return 0;
}

// Tree-aware sparse CSG. op: 0=union, 1=intersection, 2=difference.
int tvdb_py_grid_csg(const tvdb_grid_t *a, const tvdb_grid_t *b, int op,
                     int32_t **out_coords, float **out_values, size_t *out_count) {
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    bool ok = false;
    if (op == 0)      ok = tvdb_grid_csg_union(a, b, &sg);
    else if (op == 1) ok = tvdb_grid_csg_intersection(a, b, &sg);
    else if (op == 2) ok = tvdb_grid_csg_difference(a, b, &sg);
    if (!ok) {
        tvdb_sparse_grid_free(&sg);
        snprintf(s_error_msg, sizeof(s_error_msg), "grid_csg failed");
        return -1;
    }
    *out_count = sg.count;
    if (sg.count == 0) {
        *out_coords = NULL; *out_values = NULL;
        tvdb_sparse_grid_free(&sg);
        return 0;
    }
    *out_coords = (int32_t *)malloc(sg.count * 3 * sizeof(int32_t));
    *out_values = (float *)malloc(sg.count * sizeof(float));
    if (!*out_coords || !*out_values) {
        free(*out_coords); free(*out_values);
        tvdb_sparse_grid_free(&sg);
        return -1;
    }
    for (size_t i = 0; i < sg.count; ++i) {
        (*out_coords)[3*i + 0] = sg.coords[i].x;
        (*out_coords)[3*i + 1] = sg.coords[i].y;
        (*out_coords)[3*i + 2] = sg.coords[i].z;
    }
    memcpy(*out_values, sg.values, sg.count * sizeof(float));
    tvdb_sparse_grid_free(&sg);
    return 0;
}

int tvdb_py_grid_to_sparse(const tvdb_grid_t *grid,
                           int32_t **out_coords, float **out_values,
                           size_t *out_count) {
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    if (!tvdb_grid_to_sparse(grid, &sg)) {
        tvdb_sparse_grid_free(&sg);
        snprintf(s_error_msg, sizeof(s_error_msg), "grid_to_sparse failed");
        return -1;
    }
    *out_count = sg.count;
    if (sg.count == 0) {
        *out_coords = NULL; *out_values = NULL;
        tvdb_sparse_grid_free(&sg);
        return 0;
    }
    *out_coords = (int32_t *)malloc(sg.count * 3 * sizeof(int32_t));
    *out_values = (float *)malloc(sg.count * sizeof(float));
    if (!*out_coords || !*out_values) {
        free(*out_coords); free(*out_values);
        tvdb_sparse_grid_free(&sg);
        return -1;
    }
    for (size_t i = 0; i < sg.count; ++i) {
        (*out_coords)[3*i + 0] = sg.coords[i].x;
        (*out_coords)[3*i + 1] = sg.coords[i].y;
        (*out_coords)[3*i + 2] = sg.coords[i].z;
    }
    memcpy(*out_values, sg.values, sg.count * sizeof(float));
    tvdb_sparse_grid_free(&sg);
    return 0;
}

/* Typed active-voxel extraction. The float sparse-grid path is float-only, so
   we walk leaves via the (type-agnostic) hierarchy traversal — which yields the
   correct per-leaf world origin — and emit, for every active voxel, its
   world-voxel coord and a verbatim copy of the leaf's element bytes. Output:
   out_coords = int32[count*3], out_values = count * tvdb_value_type_size(vt)
   bytes, out_value_type = the leaf-level value type. Both buffers are malloc'd
   (caller frees); NULL when count == 0. Returns 0 on success, -1 on error. */
typedef struct {
    std::vector<int32_t> coords;
    std::vector<uint8_t> values;
    size_t vsize;
} typed_sparse_acc_t;

static int typed_sparse_visit(const tvdb_leaf_view_t *leaf, void *user) {
    typed_sparse_acc_t *a = (typed_sparse_acc_t *)user;
    int log2dim = leaf->log2dim;
    int dim = 1 << log2dim;
    int mask = dim - 1;
    int nslots = 1 << (3 * log2dim);
    /* leaf->data is the raw byte buffer typed as float* in the view. */
    const uint8_t *bytes = (const uint8_t *)leaf->data;
    /* OpenVDB leaf layout: slot = (x<<2L) | (y<<L) | z within the dim^3 block. */
    for (int s = 0; s < nslots; ++s) {
        if (!tvdb_nodemask_is_on(leaf->value_mask, s)) continue;
        int lx = (s >> (2 * log2dim)) & mask;
        int ly = (s >> log2dim) & mask;
        int lz = s & mask;
        a->coords.push_back(leaf->origin[0] + lx);
        a->coords.push_back(leaf->origin[1] + ly);
        a->coords.push_back(leaf->origin[2] + lz);
        a->values.insert(a->values.end(), bytes + (size_t)s * a->vsize,
                         bytes + (size_t)(s + 1) * a->vsize);
    }
    return 0;
}

int tvdb_py_grid_to_sparse_typed(const tvdb_grid_t *grid,
                                 int32_t **out_coords, void **out_values,
                                 size_t *out_count, int *out_value_type) {
    *out_coords = NULL; *out_values = NULL; *out_count = 0;
    if (!grid) {
        snprintf(s_error_msg, sizeof(s_error_msg), "to_sparse_typed: NULL grid");
        return -1;
    }
    int num_levels = grid->tree.layout.num_levels;
    if (num_levels <= 0) {
        snprintf(s_error_msg, sizeof(s_error_msg), "to_sparse_typed: empty layout");
        return -1;
    }
    tvdb_value_type_t vt = grid->tree.layout.levels[num_levels - 1].value_type;
    size_t vsize = tvdb_value_type_size(vt);
    *out_value_type = (int)vt;
    if (vsize == 0) {
        snprintf(s_error_msg, sizeof(s_error_msg), "to_sparse_typed: unsupported value type");
        return -1;
    }

    typed_sparse_acc_t acc;
    acc.vsize = vsize;
    tvdb_grid_visit_leaves(grid, typed_sparse_visit, &acc);

    size_t total = acc.coords.size() / 3;
    *out_count = total;
    if (total == 0) return 0;

    int32_t *coords = (int32_t *)malloc(total * 3 * sizeof(int32_t));
    uint8_t *vals = (uint8_t *)malloc(total * vsize);
    if (!coords || !vals) {
        free(coords); free(vals);
        snprintf(s_error_msg, sizeof(s_error_msg), "to_sparse_typed: alloc failed");
        return -1;
    }
    memcpy(coords, acc.coords.data(), total * 3 * sizeof(int32_t));
    memcpy(vals, acc.values.data(), total * vsize);
    *out_coords = coords;
    *out_values = vals;
    return 0;
}

int tvdb_py_merge_grids(const float *a_data, int a_nx, int a_ny, int a_nz,
                        float a_vs, float a_ox, float a_oy, float a_oz,
                        const float *b_data, int b_nx, int b_ny, int b_nz,
                        float b_vs, float b_ox, float b_oy, float b_oz,
                        float background,
                        float **out_data, int *out_nx, int *out_ny, int *out_nz,
                        float *out_vs, float *out_ox_, float *out_oy_, float *out_oz_) {
    tvdb_dense_grid A = make_grid(a_data, a_nx, a_ny, a_nz, a_vs, a_ox, a_oy, a_oz);
    tvdb_dense_grid B = make_grid(b_data, b_nx, b_ny, b_nz, b_vs, b_ox, b_oy, b_oz);
    tvdb_dense_grid out;
    tvdb_dense_grid_init(&out, 0, 0, 0);
    bool ok = tvdb_merge_grids(&A, &B, background, &out, NULL);
    if (!ok) {
        tvdb_dense_grid_free(&A); tvdb_dense_grid_free(&B); tvdb_dense_grid_free(&out);
        snprintf(s_error_msg, sizeof(s_error_msg), "merge_grids: voxel_size mismatch");
        return -1;
    }
    *out_nx = out.nx; *out_ny = out.ny; *out_nz = out.nz;
    *out_vs = out.voxel_size;
    *out_ox_ = out.ox; *out_oy_ = out.oy; *out_oz_ = out.oz;
    size_t N = (size_t)out.nx * out.ny * out.nz;
    *out_data = (float *)malloc(N * sizeof(float));
    if (*out_data) memcpy(*out_data, out.data, N * sizeof(float));
    tvdb_dense_grid_free(&A); tvdb_dense_grid_free(&B); tvdb_dense_grid_free(&out);
    return *out_data ? 0 : -1;
}

/* ---- Level-set primitives + SDF utilities (tinyvdb_levelset.h) ----
   Each bridge transfers ownership of the generated grid's malloc'd data to the
   caller (the Python DenseGrid wrapper frees it) and reports the grid's dims +
   transform. Returns 0 on success, -1 on error. */
static int lvl_transfer(tvdb_dense_grid *g, int ok,
                        float **out_data, int *nx, int *ny, int *nz,
                        float *ovs, float *ox, float *oy, float *oz) {
    if (!ok || !g->data) {
        snprintf(s_error_msg, sizeof(s_error_msg), "level_set: build failed");
        if (g->data) tvdb_dense_grid_free(g);
        return -1;
    }
    *out_data = g->data;  /* transfer ownership; do NOT free g */
    *nx = g->nx; *ny = g->ny; *nz = g->nz;
    *ovs = g->voxel_size; *ox = g->ox; *oy = g->oy; *oz = g->oz;
    return 0;
}

int tvdb_py_level_set_sphere(float radius, float cx, float cy, float cz,
                             float voxel_size, float half_width,
                             float **out_data, int *nx, int *ny, int *nz,
                             float *ovs, float *ox, float *oy, float *oz) {
    tvdb_dense_grid g = {}; float c[3] = { cx, cy, cz };
    int ok = tvdb_level_set_sphere(radius, c, voxel_size, half_width, &g);
    return lvl_transfer(&g, ok, out_data, nx, ny, nz, ovs, ox, oy, oz);
}

int tvdb_py_level_set_box(float hex, float hey, float hez,
                          float cx, float cy, float cz,
                          float voxel_size, float half_width,
                          float **out_data, int *nx, int *ny, int *nz,
                          float *ovs, float *ox, float *oy, float *oz) {
    tvdb_dense_grid g = {}; float he[3] = { hex, hey, hez }; float c[3] = { cx, cy, cz };
    int ok = tvdb_level_set_box(he, c, voxel_size, half_width, &g);
    return lvl_transfer(&g, ok, out_data, nx, ny, nz, ovs, ox, oy, oz);
}

int tvdb_py_level_set_torus(float major_radius, float minor_radius,
                            float cx, float cy, float cz,
                            float voxel_size, float half_width,
                            float **out_data, int *nx, int *ny, int *nz,
                            float *ovs, float *ox, float *oy, float *oz) {
    tvdb_dense_grid g = {}; float c[3] = { cx, cy, cz };
    int ok = tvdb_level_set_torus(major_radius, minor_radius, c, voxel_size,
                                  half_width, &g);
    return lvl_transfer(&g, ok, out_data, nx, ny, nz, ovs, ox, oy, oz);
}

int tvdb_py_level_set_capsule(float p0x, float p0y, float p0z,
                              float p1x, float p1y, float p1z, float radius,
                              float voxel_size, float half_width,
                              float **out_data, int *nx, int *ny, int *nz,
                              float *ovs, float *ox, float *oy, float *oz) {
    tvdb_dense_grid g = {};
    float p0[3] = { p0x, p0y, p0z }, p1[3] = { p1x, p1y, p1z };
    int ok = tvdb_level_set_capsule(p0, p1, radius, voxel_size, half_width, &g);
    return lvl_transfer(&g, ok, out_data, nx, ny, nz, ovs, ox, oy, oz);
}

int tvdb_py_level_set_platonic(int face_count, float radius,
                               float cx, float cy, float cz,
                               float voxel_size, float half_width,
                               float **out_data, int *nx, int *ny, int *nz,
                               float *ovs, float *ox, float *oy, float *oz) {
    tvdb_dense_grid g = {}; float c[3] = { cx, cy, cz };
    int ok = tvdb_level_set_platonic(face_count, radius, c, voxel_size, half_width, &g);
    return lvl_transfer(&g, ok, out_data, nx, ny, nz, ovs, ox, oy, oz);
}

/* SDF utilities: input is an existing dense grid (data + dims + transform);
   output has the same dims/transform, data malloc'd into *out_data. */
int tvdb_py_sdf_to_fog_volume(const float *data, int nx, int ny, int nz,
                              float vs, float ox, float oy, float oz,
                              float half_width, float **out_data) {
    tvdb_dense_grid in;
    in.nx = nx; in.ny = ny; in.nz = nz; in.voxel_size = vs;
    in.ox = ox; in.oy = oy; in.oz = oz; in.data = (float *)data;
    tvdb_dense_grid out;
    if (!tvdb_sdf_to_fog_volume(&in, half_width, &out)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "sdf_to_fog_volume failed");
        return -1;
    }
    *out_data = out.data;  /* transfer ownership */
    return 0;
}

int tvdb_py_sdf_interior_mask(const float *data, int nx, int ny, int nz,
                              float vs, float ox, float oy, float oz,
                              float isovalue, float **out_data) {
    tvdb_dense_grid in;
    in.nx = nx; in.ny = ny; in.nz = nz; in.voxel_size = vs;
    in.ox = ox; in.oy = oy; in.oz = oz; in.data = (float *)data;
    tvdb_dense_grid out;
    if (!tvdb_sdf_interior_mask(&in, isovalue, &out)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "sdf_interior_mask failed");
        return -1;
    }
    *out_data = out.data;  /* transfer ownership */
    return 0;
}

/* Segment the interior into connected components. The output grids all share
   the input's dims/transform, so we hand back just their data buffers in
   *out_list (a malloc'd array of *out_count float*, each owned by the caller).
   Returns 0 on success, -1 on error. */
int tvdb_py_sdf_segmentation(const float *data, int nx, int ny, int nz,
                             float isovalue, int connectivity,
                             float ***out_list, int *out_count) {
    *out_list = NULL; *out_count = 0;
    tvdb_dense_grid in;
    in.nx = nx; in.ny = ny; in.nz = nz; in.voxel_size = 1.0f;
    in.ox = in.oy = in.oz = 0.0f; in.data = (float *)data;
    tvdb_dense_grid *segs = NULL; int count = 0;
    if (!tvdb_sdf_segmentation(&in, isovalue, connectivity, &segs, &count)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "sdf_segmentation failed");
        return -1;
    }
    *out_count = count;
    if (count == 0) return 0;
    float **list = (float **)malloc((size_t)count * sizeof(float *));
    if (!list) {
        for (int c = 0; c < count; ++c) tvdb_dense_grid_free(&segs[c]);
        free(segs);
        snprintf(s_error_msg, sizeof(s_error_msg), "sdf_segmentation: alloc failed");
        return -1;
    }
    for (int c = 0; c < count; ++c) list[c] = segs[c].data;  /* transfer */
    free(segs);  /* struct array only; data buffers transferred */
    *out_list = list;
    return 0;
}

int tvdb_py_sdf_extract_enclosed(const float *data, int nx, int ny, int nz,
                                 float isovalue, int connectivity, float **out) {
    tvdb_dense_grid in;
    in.nx = nx; in.ny = ny; in.nz = nz; in.voxel_size = 1.0f;
    in.ox = in.oy = in.oz = 0.0f; in.data = (float *)data;
    tvdb_dense_grid mask;
    if (!tvdb_sdf_extract_enclosed_regions(&in, isovalue, connectivity, &mask)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "sdf_extract_enclosed_regions failed");
        return -1;
    }
    *out = mask.data;  /* transfer ownership */
    return 0;
}

double tvdb_py_level_set_euler(const float *data, int nx, int ny, int nz,
                               float isovalue) {
    tvdb_dense_grid in;
    in.nx = nx; in.ny = ny; in.nz = nz; in.voxel_size = 1.0f;
    in.ox = in.oy = in.oz = 0.0f; in.data = (float *)data;
    return tvdb_level_set_euler_characteristic(&in, isovalue);
}

int tvdb_py_level_set_genus(const float *data, int nx, int ny, int nz,
                            float isovalue) {
    tvdb_dense_grid in;
    in.nx = nx; in.ny = ny; in.nz = nz; in.voxel_size = 1.0f;
    in.ox = in.oy = in.oz = 0.0f; in.data = (float *)data;
    return tvdb_level_set_genus(&in, isovalue);
}

/* ---- Statistics / diagnostics (tinyvdb_stats.h) ---- */

int tvdb_py_grid_statistics(const float *data, int nx, int ny, int nz,
                            double *mn, double *mx, double *mean,
                            double *stddev, double *sum, size_t *count) {
    tvdb_dense_grid g;
    g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = 1.0f;
    g.ox = g.oy = g.oz = 0.0f; g.data = (float *)data;
    tvdb_grid_stats_t s;
    if (!tvdb_grid_statistics(&g, &s)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "grid_statistics failed");
        return -1;
    }
    *mn = s.min; *mx = s.max; *mean = s.mean;
    *stddev = s.stddev; *sum = s.sum; *count = s.count;
    return 0;
}

/* Histogram: returns *out_counts as a malloc'd array of `nbins` int64. */
int tvdb_py_grid_histogram(const float *data, int nx, int ny, int nz,
                           double rmin, double rmax, int nbins,
                           int64_t **out_counts) {
    *out_counts = NULL;
    tvdb_dense_grid g;
    g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = 1.0f;
    g.ox = g.oy = g.oz = 0.0f; g.data = (float *)data;
    size_t *tmp = (size_t *)malloc((size_t)nbins * sizeof(size_t));
    if (!tmp) { snprintf(s_error_msg, sizeof(s_error_msg), "histogram alloc"); return -1; }
    if (!tvdb_grid_histogram(&g, rmin, rmax, nbins, tmp)) {
        free(tmp);
        snprintf(s_error_msg, sizeof(s_error_msg), "grid_histogram failed");
        return -1;
    }
    int64_t *out = (int64_t *)malloc((size_t)nbins * sizeof(int64_t));
    if (!out) { free(tmp); snprintf(s_error_msg, sizeof(s_error_msg), "histogram alloc"); return -1; }
    for (int b = 0; b < nbins; ++b) out[b] = (int64_t)tmp[b];
    free(tmp);
    *out_counts = out;
    return 0;
}

int tvdb_py_check_level_set(const float *data, int nx, int ny, int nz, float vs,
                            double band_world, double tol,
                            double *mean_grad, double *max_err,
                            double *bad_frac, int64_t *band_count) {
    tvdb_dense_grid g;
    g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = vs;
    g.ox = g.oy = g.oz = 0.0f; g.data = (float *)data;
    tvdb_level_set_check_t c;
    if (!tvdb_check_level_set(&g, band_world, tol, &c)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "check_level_set failed");
        return -1;
    }
    *mean_grad = c.mean_grad_mag; *max_err = c.max_grad_error;
    *bad_frac = c.bad_fraction; *band_count = (int64_t)c.band_count;
    return 0;
}

int tvdb_py_check_fog_volume(const float *data, int nx, int ny, int nz,
                             double eps, int *valid, double *mn, double *mx) {
    tvdb_dense_grid g;
    g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = 1.0f;
    g.ox = g.oy = g.oz = 0.0f; g.data = (float *)data;
    if (!tvdb_check_fog_volume(&g, eps, valid, mn, mx)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "check_fog_volume failed");
        return -1;
    }
    return 0;
}

/* ---- Vector operators / composite / filters (tinyvdb_ops.h) ---- */

int tvdb_py_magnitude(const float *vdata, int nx, int ny, int nz, float **out) {
    size_t nvox = (size_t)nx * ny * nz;
    *out = (float *)malloc(nvox * sizeof(float));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "magnitude alloc"); return -1; }
    tvdb_dense_vec_grid v; v.nx = nx; v.ny = ny; v.nz = nz; v.voxel_size = 1.0f;
    v.ox = v.oy = v.oz = 0.0f; v.data = (float *)vdata;
    tvdb_dense_grid o; o.nx = nx; o.ny = ny; o.nz = nz; o.voxel_size = 1.0f;
    o.ox = o.oy = o.oz = 0.0f; o.data = *out;
    tvdb_magnitude(&v, &o);
    return 0;
}

int tvdb_py_normalize_vec(const float *vdata, int nx, int ny, int nz, float **out) {
    size_t nvox = (size_t)nx * ny * nz;
    *out = (float *)malloc(nvox * 3 * sizeof(float));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "normalize alloc"); return -1; }
    tvdb_dense_vec_grid v; v.nx = nx; v.ny = ny; v.nz = nz; v.voxel_size = 1.0f;
    v.ox = v.oy = v.oz = 0.0f; v.data = (float *)vdata;
    tvdb_dense_vec_grid o; o.nx = nx; o.ny = ny; o.nz = nz; o.voxel_size = 1.0f;
    o.ox = o.oy = o.oz = 0.0f; o.data = *out;
    tvdb_normalize_vec(&v, &o);
    return 0;
}

int tvdb_py_cpt(const float *data, int nx, int ny, int nz, float vs,
                float ox, float oy, float oz, float **out) {
    size_t nvox = (size_t)nx * ny * nz;
    *out = (float *)malloc(nvox * 3 * sizeof(float));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "cpt alloc"); return -1; }
    tvdb_dense_grid s; s.nx = nx; s.ny = ny; s.nz = nz; s.voxel_size = vs;
    s.ox = ox; s.oy = oy; s.oz = oz; s.data = (float *)data;
    tvdb_dense_vec_grid o; o.nx = nx; o.ny = ny; o.nz = nz; o.voxel_size = vs;
    o.ox = ox; o.oy = oy; o.oz = oz; o.data = *out;
    tvdb_cpt(&s, &o);
    return 0;
}

/* op: 0 max, 1 min, 2 sum, 3 mult */
int tvdb_py_composite(const float *a, const float *b, int nx, int ny, int nz,
                      int op, float **out) {
    size_t nvox = (size_t)nx * ny * nz;
    *out = (float *)malloc(nvox * sizeof(float));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "composite alloc"); return -1; }
    tvdb_dense_grid ga, gb, gr;
    ga.nx = gb.nx = gr.nx = nx; ga.ny = gb.ny = gr.ny = ny; ga.nz = gb.nz = gr.nz = nz;
    ga.voxel_size = gb.voxel_size = gr.voxel_size = 1.0f;
    ga.ox = ga.oy = ga.oz = gb.ox = gb.oy = gb.oz = gr.ox = gr.oy = gr.oz = 0.0f;
    ga.data = (float *)a; gb.data = (float *)b; gr.data = *out;
    switch (op) {
        case 0: tvdb_comp_max(&ga, &gb, &gr); break;
        case 1: tvdb_comp_min(&ga, &gb, &gr); break;
        case 2: tvdb_comp_sum(&ga, &gb, &gr); break;
        case 3: tvdb_comp_mult(&ga, &gb, &gr); break;
        default: snprintf(s_error_msg, sizeof(s_error_msg), "composite: bad op"); free(*out); *out = NULL; return -1;
    }
    return 0;
}

int tvdb_py_median_filter(const float *data, int nx, int ny, int nz,
                          int radius, int iterations, float **out) {
    size_t nvox = (size_t)nx * ny * nz;
    *out = (float *)malloc(nvox * sizeof(float));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "median alloc"); return -1; }
    memcpy(*out, data, nvox * sizeof(float));
    tvdb_dense_grid g; g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = 1.0f;
    g.ox = g.oy = g.oz = 0.0f; g.data = *out;
    tvdb_median_filter(&g, radius, iterations);  // in place on the copy
    return 0;
}

int tvdb_py_mean_curvature_flow(const float *data, int nx, int ny, int nz,
                                float vs, float dt, int iterations, float **out) {
    size_t nvox = (size_t)nx * ny * nz;
    *out = (float *)malloc(nvox * sizeof(float));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "mcf alloc"); return -1; }
    memcpy(*out, data, nvox * sizeof(float));
    tvdb_dense_grid g; g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = vs;
    g.ox = g.oy = g.oz = 0.0f; g.data = *out;
    tvdb_mean_curvature_flow(&g, dt, iterations);
    return 0;
}

int tvdb_py_signed_flood_fill(const float *data, int nx, int ny, int nz,
                              float band_world, float **out) {
    size_t nvox = (size_t)nx * ny * nz;
    *out = (float *)malloc(nvox * sizeof(float));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "flood alloc"); return -1; }
    memcpy(*out, data, nvox * sizeof(float));
    tvdb_dense_grid g; g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = 1.0f;
    g.ox = g.oy = g.oz = 0.0f; g.data = *out;
    tvdb_signed_flood_fill(&g, band_world);
    return 0;
}

/* ---- Coordinate utilities & spatial queries (tinyvdb_grid_index.h) ---- */

int tvdb_py_morton_encode(const int32_t *ijk, size_t n, uint64_t **out) {
    *out = (uint64_t *)malloc(n * sizeof(uint64_t));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "morton alloc"); return -1; }
    for (size_t i = 0; i < n; ++i)
        (*out)[i] = tvdb_morton_encode(ijk[3*i], ijk[3*i+1], ijk[3*i+2]);
    return 0;
}

int tvdb_py_morton_decode(const uint64_t *codes, size_t n, int32_t **out) {
    *out = (int32_t *)malloc(n * 3 * sizeof(int32_t));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "morton alloc"); return -1; }
    for (size_t i = 0; i < n; ++i)
        tvdb_morton_decode(codes[i], &(*out)[3*i], &(*out)[3*i+1], &(*out)[3*i+2]);
    return 0;
}

int tvdb_py_voxelize_points(const float *pts, size_t n,
                            float vsx, float vsy, float vsz,
                            float ox, float oy, float oz,
                            int32_t **out, size_t *out_count) {
    float vs[3] = { vsx, vsy, vsz }, org[3] = { ox, oy, oz };
    if (!tvdb_voxelize_points(pts, n, vs, org, out, out_count)) {
        snprintf(s_error_msg, sizeof(s_error_msg), "voxelize_points failed");
        return -1;
    }
    return 0;
}

int tvdb_py_coords_in_set(const int32_t *active, size_t na,
                          const int32_t *query, size_t nq, uint8_t **out) {
    *out = (uint8_t *)malloc(nq ? nq : 1);
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "coords_in_set alloc"); return -1; }
    if (!tvdb_coords_in_set(active, na, query, nq, *out)) {
        free(*out); *out = NULL;
        snprintf(s_error_msg, sizeof(s_error_msg), "coords_in_set failed");
        return -1;
    }
    return 0;
}

int tvdb_py_points_in_set(const float *pts, size_t np,
                          float vsx, float vsy, float vsz,
                          float ox, float oy, float oz,
                          const int32_t *active, size_t na, uint8_t **out) {
    float vs[3] = { vsx, vsy, vsz }, org[3] = { ox, oy, oz };
    *out = (uint8_t *)malloc(np ? np : 1);
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "points_in_set alloc"); return -1; }
    if (!tvdb_points_in_set(pts, np, vs, org, active, na, *out)) {
        free(*out); *out = NULL;
        snprintf(s_error_msg, sizeof(s_error_msg), "points_in_set failed");
        return -1;
    }
    return 0;
}

int tvdb_py_ijk_to_index(const int32_t *active, size_t na,
                         const int32_t *query, size_t nq, int64_t **out) {
    *out = (int64_t *)malloc((nq ? nq : 1) * sizeof(int64_t));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "ijk_to_index alloc"); return -1; }
    if (!tvdb_ijk_to_index(active, na, query, nq, *out)) {
        free(*out); *out = NULL;
        snprintf(s_error_msg, sizeof(s_error_msg), "ijk_to_index failed");
        return -1;
    }
    return 0;
}

int tvdb_py_volume_render(const float *data, int nx, int ny, int nz, float vs,
                          float ox, float oy, float oz,
                          float ex, float ey, float ez,
                          float cx, float cy, float cz,
                          float ux, float uy, float uz,
                          float fov_y, int width, int height,
                          float sigma, float step, float background,
                          float **out_img) {
    tvdb_dense_grid g;
    g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = vs;
    g.ox = ox; g.oy = oy; g.oz = oz; g.data = (float *)data;
    *out_img = (float *)malloc((size_t)width * height * sizeof(float));
    if (!*out_img) { snprintf(s_error_msg, sizeof(s_error_msg), "volume_render alloc"); return -1; }
    float eye[3] = { ex, ey, ez }, center[3] = { cx, cy, cz }, up[3] = { ux, uy, uz };
    if (!tvdb_volume_render(&g, eye, center, up, fov_y, width, height,
                            sigma, step, background, *out_img)) {
        free(*out_img); *out_img = NULL;
        snprintf(s_error_msg, sizeof(s_error_msg), "volume_render failed");
        return -1;
    }
    return 0;
}

int tvdb_py_neighbor_counts(const int32_t *active, size_t na,
                            int connectivity, int32_t **out) {
    *out = (int32_t *)malloc((na ? na : 1) * sizeof(int32_t));
    if (!*out) { snprintf(s_error_msg, sizeof(s_error_msg), "neighbor_counts alloc"); return -1; }
    if (!tvdb_neighbor_counts(active, na, connectivity, *out)) {
        free(*out); *out = NULL;
        snprintf(s_error_msg, sizeof(s_error_msg), "neighbor_counts failed");
        return -1;
    }
    return 0;
}

/* Rebuild a clean SDF from the isosurface. The output has its own dims and
   transform (sized by mesh-to-SDF), so report all of them; out_data is the
   transferred malloc'd buffer. Returns 0 on success, -1 on error. */
int tvdb_py_level_set_rebuild(const float *data, int nx, int ny, int nz,
                              float vs, float ox, float oy, float oz,
                              float isovalue, float voxel_size, float half_width,
                              int sign_method,
                              float **out_data, int *onx, int *ony, int *onz,
                              float *ovs, float *oox, float *ooy, float *ooz) {
    tvdb_dense_grid in;
    in.nx = nx; in.ny = ny; in.nz = nz; in.voxel_size = vs;
    in.ox = ox; in.oy = oy; in.oz = oz; in.data = (float *)data;
    tvdb_dense_grid out = {};
    if (!tvdb_level_set_rebuild(&in, isovalue, voxel_size, half_width, sign_method, &out)) {
        if (out.data) tvdb_dense_grid_free(&out);
        snprintf(s_error_msg, sizeof(s_error_msg),
                 "level_set_rebuild failed (empty isosurface?)");
        return -1;
    }
    *out_data = out.data;  /* transfer */
    *onx = out.nx; *ony = out.ny; *onz = out.nz;
    *ovs = out.voxel_size; *oox = out.ox; *ooy = out.oy; *ooz = out.oz;
    return 0;
}

} /* extern "C" */
