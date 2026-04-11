/*
 * _tinyvdb_mesh_ops.cc — extern "C" wrappers for tinyvdb_mesh.h / tinyvdb_ops.h
 *
 * Compiled as C++11, exposes plain-C functions callable from _tinyvdb.c.
 * All data is exchanged via flat arrays (float*, uint32_t*) and sizes.
 */

#define TINYVDB_MESH_IMPLEMENTATION
#include "tinyvdb_mesh.h"

#define TINYVDB_OPS_IMPLEMENTATION
#include "tinyvdb_ops.h"

#include <cstring>
#include <cstdlib>
#include <string>

/* Thread-local error message buffer */
static thread_local char s_error_msg[512] = {0};

extern "C" {

const char *tvdb_py_last_error(void) { return s_error_msg; }

/* ======================================================================== */
/*  Helpers                                                                  */
/* ======================================================================== */

static tvdb_mesh::DenseGrid make_grid(const float *data, int nx, int ny, int nz,
                                      float voxel_size, float ox, float oy,
                                      float oz) {
    tvdb_mesh::DenseGrid g;
    g.nx = nx; g.ny = ny; g.nz = nz;
    g.ox = ox; g.oy = oy; g.oz = oz;
    g.voxel_size = voxel_size;
    g.data.assign(data, data + (size_t)nx * ny * nz);
    return g;
}

static tvdb_ops::DenseVecGrid make_vec_grid(const float *data, int nx, int ny,
                                            int nz, float voxel_size,
                                            float ox, float oy, float oz) {
    tvdb_ops::DenseVecGrid g;
    g.nx = nx; g.ny = ny; g.nz = nz;
    g.ox = ox; g.oy = oy; g.oz = oz;
    g.voxel_size = voxel_size;
    g.data.assign(data, data + (size_t)nx * ny * nz * 3);
    return g;
}

/* Copy DenseGrid data out to caller-allocated buffer.
   Caller must free *out_data with free(). */
static void export_grid(const tvdb_mesh::DenseGrid &g, float **out_data,
                        int *nx, int *ny, int *nz, float *voxel_size,
                        float *ox, float *oy, float *oz) {
    *nx = g.nx; *ny = g.ny; *nz = g.nz;
    *voxel_size = g.voxel_size;
    *ox = g.ox; *oy = g.oy; *oz = g.oz;
    size_t n = (size_t)g.nx * g.ny * g.nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, g.data.data(), n * sizeof(float));
}

static void export_vec_grid(const tvdb_ops::DenseVecGrid &g, float **out_data,
                            int *nx, int *ny, int *nz, float *voxel_size,
                            float *ox, float *oy, float *oz) {
    *nx = g.nx; *ny = g.ny; *nz = g.nz;
    *voxel_size = g.voxel_size;
    *ox = g.ox; *oy = g.oy; *oz = g.oz;
    size_t n = (size_t)g.nx * g.ny * g.nz * 3;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, g.data.data(), n * sizeof(float));
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
    tvdb_mesh::TriangleMesh mesh;
    mesh.vertices.resize(nv);
    memcpy(mesh.vertices.data(), verts, nv * sizeof(tvdb_mesh::Vec3f));
    mesh.faces.resize(nt);
    memcpy(mesh.faces.data(), tris, nt * sizeof(tvdb_mesh::Triangle));

    tvdb_mesh::DenseGrid grid;
    bool ok = tvdb_mesh::MeshToSDF_VDB(
        mesh, voxel_size, band_width, &grid,
        static_cast<tvdb_mesh::SignMethod>(sign_method));
    if (!ok) {
        snprintf(s_error_msg, sizeof(s_error_msg), "MeshToSDF_VDB failed");
        return -1;
    }
    export_grid(grid, out_data, nx, ny, nz, out_voxel_size, ox, oy, oz);
    return 0;
}

int tvdb_py_sdf_to_mesh(const float *data, int nx, int ny, int nz,
                        float voxel_size, float ox, float oy, float oz,
                        float isovalue,
                        float **out_verts, size_t *out_nv,
                        uint32_t **out_tris, size_t *out_nt) {
    tvdb_mesh::DenseGrid grid = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::TriangleMesh mesh;
    bool ok = tvdb_mesh::SDFToMesh(grid, isovalue, &mesh);
    if (!ok) {
        snprintf(s_error_msg, sizeof(s_error_msg), "SDFToMesh failed");
        return -1;
    }
    *out_nv = mesh.vertices.size();
    *out_nt = mesh.faces.size();
    *out_verts = (float *)malloc(*out_nv * sizeof(tvdb_mesh::Vec3f));
    *out_tris = (uint32_t *)malloc(*out_nt * sizeof(tvdb_mesh::Triangle));
    if (*out_verts) memcpy(*out_verts, mesh.vertices.data(), *out_nv * sizeof(tvdb_mesh::Vec3f));
    if (*out_tris) memcpy(*out_tris, mesh.faces.data(), *out_nt * sizeof(tvdb_mesh::Triangle));
    return 0;
}

int tvdb_py_make_manifold(const float *verts, size_t nv,
                          const uint32_t *tris, size_t nt,
                          double resolution, double isovalue, int sign_method,
                          float **out_verts, size_t *out_nv,
                          uint32_t **out_tris, size_t *out_nt) {
    tvdb_mesh::TriangleMesh input;
    input.vertices.resize(nv);
    memcpy(input.vertices.data(), verts, nv * sizeof(tvdb_mesh::Vec3f));
    input.faces.resize(nt);
    memcpy(input.faces.data(), tris, nt * sizeof(tvdb_mesh::Triangle));

    tvdb_mesh::TriangleMesh output;
    bool ok = tvdb_mesh::MakeManifold_VDB(
        input, resolution, isovalue, &output,
        static_cast<tvdb_mesh::SignMethod>(sign_method));
    if (!ok) {
        snprintf(s_error_msg, sizeof(s_error_msg), "MakeManifold_VDB failed");
        return -1;
    }
    *out_nv = output.vertices.size();
    *out_nt = output.faces.size();
    *out_verts = (float *)malloc(*out_nv * sizeof(tvdb_mesh::Vec3f));
    *out_tris = (uint32_t *)malloc(*out_nt * sizeof(tvdb_mesh::Triangle));
    if (*out_verts) memcpy(*out_verts, output.vertices.data(), *out_nv * sizeof(tvdb_mesh::Vec3f));
    if (*out_tris) memcpy(*out_tris, output.faces.data(), *out_nt * sizeof(tvdb_mesh::Triangle));
    return 0;
}

/* ======================================================================== */
/*  Ops: Morphology (in-place)                                              */
/* ======================================================================== */

int tvdb_py_dilate(float *data, int nx, int ny, int nz,
                   float voxel_size, float ox, float oy, float oz,
                   int iterations) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::Dilate(&g, iterations);
    memcpy(data, g.data.data(), (size_t)nx * ny * nz * sizeof(float));
    return 0;
}

int tvdb_py_erode(float *data, int nx, int ny, int nz,
                  float voxel_size, float ox, float oy, float oz,
                  int iterations) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::Erode(&g, iterations);
    memcpy(data, g.data.data(), (size_t)nx * ny * nz * sizeof(float));
    return 0;
}

int tvdb_py_open(float *data, int nx, int ny, int nz,
                 float voxel_size, float ox, float oy, float oz,
                 int iterations) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::Open(&g, iterations);
    memcpy(data, g.data.data(), (size_t)nx * ny * nz * sizeof(float));
    return 0;
}

int tvdb_py_close(float *data, int nx, int ny, int nz,
                  float voxel_size, float ox, float oy, float oz,
                  int iterations) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::Close(&g, iterations);
    memcpy(data, g.data.data(), (size_t)nx * ny * nz * sizeof(float));
    return 0;
}

/* ======================================================================== */
/*  Ops: Filtering (in-place)                                               */
/* ======================================================================== */

int tvdb_py_gaussian_filter(float *data, int nx, int ny, int nz,
                            float voxel_size, float ox, float oy, float oz,
                            int width, int iterations) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::GaussianFilter(&g, width, iterations);
    memcpy(data, g.data.data(), (size_t)nx * ny * nz * sizeof(float));
    return 0;
}

int tvdb_py_mean_filter(float *data, int nx, int ny, int nz,
                        float voxel_size, float ox, float oy, float oz,
                        int width, int iterations) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::MeanFilter(&g, width, iterations);
    memcpy(data, g.data.data(), (size_t)nx * ny * nz * sizeof(float));
    return 0;
}

int tvdb_py_laplacian_filter(float *data, int nx, int ny, int nz,
                             float voxel_size, float ox, float oy, float oz,
                             int iterations) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::LaplacianFilter(&g, iterations);
    memcpy(data, g.data.data(), (size_t)nx * ny * nz * sizeof(float));
    return 0;
}

/* ======================================================================== */
/*  Ops: CSG                                                                */
/* ======================================================================== */

int tvdb_py_csg_union(const float *a_data, const float *b_data,
                      int nx, int ny, int nz,
                      float voxel_size, float ox, float oy, float oz,
                      float **out_data) {
    tvdb_mesh::DenseGrid a = make_grid(a_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid b = make_grid(b_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid result;
    tvdb_ops::CSGUnion(a, b, &result);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, result.data.data(), n * sizeof(float));
    return 0;
}

int tvdb_py_csg_intersection(const float *a_data, const float *b_data,
                             int nx, int ny, int nz,
                             float voxel_size, float ox, float oy, float oz,
                             float **out_data) {
    tvdb_mesh::DenseGrid a = make_grid(a_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid b = make_grid(b_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid result;
    tvdb_ops::CSGIntersection(a, b, &result);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, result.data.data(), n * sizeof(float));
    return 0;
}

int tvdb_py_csg_difference(const float *a_data, const float *b_data,
                           int nx, int ny, int nz,
                           float voxel_size, float ox, float oy, float oz,
                           float **out_data) {
    tvdb_mesh::DenseGrid a = make_grid(a_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid b = make_grid(b_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid result;
    tvdb_ops::CSGDifference(a, b, &result);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, result.data.data(), n * sizeof(float));
    return 0;
}

/* ======================================================================== */
/*  Ops: Measurement                                                        */
/* ======================================================================== */

float tvdb_py_surface_area(const float *data, int nx, int ny, int nz,
                           float voxel_size, float ox, float oy, float oz) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    return tvdb_ops::SurfaceArea(g);
}

float tvdb_py_volume(const float *data, int nx, int ny, int nz,
                     float voxel_size, float ox, float oy, float oz) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    return tvdb_ops::Volume(g);
}

/* ======================================================================== */
/*  Ops: Differential operators                                             */
/* ======================================================================== */

int tvdb_py_gradient(const float *data, int nx, int ny, int nz,
                     float voxel_size, float ox, float oy, float oz,
                     float **out_data) {
    tvdb_mesh::DenseGrid scalar = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::DenseVecGrid grad;
    tvdb_ops::Gradient(scalar, &grad);
    size_t n = (size_t)nx * ny * nz * 3;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, grad.data.data(), n * sizeof(float));
    return 0;
}

int tvdb_py_divergence(const float *vec_data, int nx, int ny, int nz,
                       float voxel_size, float ox, float oy, float oz,
                       float **out_data) {
    tvdb_ops::DenseVecGrid vec = make_vec_grid(vec_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid div_grid;
    tvdb_ops::Divergence(vec, &div_grid);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, div_grid.data.data(), n * sizeof(float));
    return 0;
}

int tvdb_py_laplacian(const float *data, int nx, int ny, int nz,
                      float voxel_size, float ox, float oy, float oz,
                      float **out_data) {
    tvdb_mesh::DenseGrid scalar = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid lap;
    tvdb_ops::Laplacian(scalar, &lap);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, lap.data.data(), n * sizeof(float));
    return 0;
}

int tvdb_py_curl(const float *vec_data, int nx, int ny, int nz,
                 float voxel_size, float ox, float oy, float oz,
                 float **out_data) {
    tvdb_ops::DenseVecGrid vec = make_vec_grid(vec_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::DenseVecGrid curl_grid;
    tvdb_ops::Curl(vec, &curl_grid);
    size_t n = (size_t)nx * ny * nz * 3;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, curl_grid.data.data(), n * sizeof(float));
    return 0;
}

/* ======================================================================== */
/*  Ops: Advection & Poisson                                                */
/* ======================================================================== */

int tvdb_py_advect(const float *field_data, const float *vel_data,
                   int nx, int ny, int nz,
                   float voxel_size, float ox, float oy, float oz,
                   float dt, float **out_data) {
    tvdb_mesh::DenseGrid field = make_grid(field_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_ops::DenseVecGrid vel = make_vec_grid(vel_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid result;
    tvdb_ops::AdvectSemiLagrangian(field, vel, dt, &result);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, result.data.data(), n * sizeof(float));
    return 0;
}

int tvdb_py_solve_poisson(const float *rhs_data, int nx, int ny, int nz,
                          float voxel_size, float ox, float oy, float oz,
                          int max_iters, float tolerance,
                          float **out_data, int *out_iters) {
    tvdb_mesh::DenseGrid rhs = make_grid(rhs_data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::DenseGrid x;
    x.nx = nx; x.ny = ny; x.nz = nz;
    x.ox = ox; x.oy = oy; x.oz = oz;
    x.voxel_size = voxel_size;
    x.data.assign((size_t)nx * ny * nz, 0.0f);
    *out_iters = tvdb_ops::SolvePoisson(rhs, &x, max_iters, tolerance);
    size_t n = (size_t)nx * ny * nz;
    *out_data = (float *)malloc(n * sizeof(float));
    if (*out_data) memcpy(*out_data, x.data.data(), n * sizeof(float));
    return 0;
}

/* ======================================================================== */
/*  Ops: Ray casting                                                        */
/* ======================================================================== */

int tvdb_py_ray_cast_sdf(const float *data, int nx, int ny, int nz,
                         float voxel_size, float ox, float oy, float oz,
                         float ray_ox, float ray_oy, float ray_oz,
                         float ray_dx, float ray_dy, float ray_dz,
                         float max_t,
                         int *out_hit, float *out_t,
                         float *out_px, float *out_py, float *out_pz,
                         float *out_nx, float *out_ny, float *out_nz) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    tvdb_mesh::Vec3f origin = {ray_ox, ray_oy, ray_oz};
    tvdb_mesh::Vec3f dir = {ray_dx, ray_dy, ray_dz};
    tvdb_ops::RayHit hit;
    *out_hit = tvdb_ops::RayCastSDF(g, origin, dir, max_t, &hit) ? 1 : 0;
    *out_t = hit.t;
    *out_px = hit.position.x; *out_py = hit.position.y; *out_pz = hit.position.z;
    *out_nx = hit.normal.x;   *out_ny = hit.normal.y;   *out_nz = hit.normal.z;
    return 0;
}

/* ======================================================================== */
/*  Ops: Particles to SDF                                                   */
/* ======================================================================== */

int tvdb_py_particles_to_sdf(const float *positions, const float *radii,
                             size_t num_particles,
                             float voxel_size, float band_width,
                             float **out_data, int *nx, int *ny, int *nz,
                             float *out_voxel_size,
                             float *ox, float *oy, float *oz) {
    std::vector<tvdb_ops::Particle> particles(num_particles);
    for (size_t i = 0; i < num_particles; i++) {
        particles[i].position = {positions[i*3], positions[i*3+1], positions[i*3+2]};
        particles[i].radius = radii[i];
    }
    tvdb_mesh::DenseGrid grid;
    tvdb_ops::ParticlesToSDF(particles, voxel_size, band_width, &grid);
    export_grid(grid, out_data, nx, ny, nz, out_voxel_size, ox, oy, oz);
    return 0;
}

/* ======================================================================== */
/*  Ops: Volume to spheres                                                  */
/* ======================================================================== */

int tvdb_py_volume_to_spheres(const float *data, int nx, int ny, int nz,
                              float voxel_size, float ox, float oy, float oz,
                              float min_radius, int max_spheres, float overlap,
                              float **out_centers, float **out_radii,
                              size_t *out_count) {
    tvdb_mesh::DenseGrid g = make_grid(data, nx, ny, nz, voxel_size, ox, oy, oz);
    std::vector<tvdb_ops::Sphere> spheres;
    tvdb_ops::VolumeToSpheres(g, &spheres, min_radius, max_spheres, overlap);
    *out_count = spheres.size();
    *out_centers = (float *)malloc(*out_count * 3 * sizeof(float));
    *out_radii = (float *)malloc(*out_count * sizeof(float));
    for (size_t i = 0; i < spheres.size(); i++) {
        (*out_centers)[i*3+0] = spheres[i].center.x;
        (*out_centers)[i*3+1] = spheres[i].center.y;
        (*out_centers)[i*3+2] = spheres[i].center.z;
        (*out_radii)[i] = spheres[i].radius;
    }
    return 0;
}

/* ======================================================================== */
/*  Ops: Fracture                                                           */
/* ======================================================================== */

int tvdb_py_fracture(const float *vol_data, int nx, int ny, int nz,
                     float voxel_size, float ox, float oy, float oz,
                     const float **cutter_datas, int num_cutters,
                     float ***out_pieces, int *out_num_pieces) {
    tvdb_mesh::DenseGrid volume = make_grid(vol_data, nx, ny, nz, voxel_size, ox, oy, oz);
    std::vector<tvdb_mesh::DenseGrid> cutters(num_cutters);
    for (int i = 0; i < num_cutters; i++) {
        cutters[i] = make_grid(cutter_datas[i], nx, ny, nz, voxel_size, ox, oy, oz);
    }
    std::vector<tvdb_mesh::DenseGrid> pieces;
    tvdb_ops::Fracture(volume, cutters, &pieces);
    *out_num_pieces = (int)pieces.size();
    size_t n = (size_t)nx * ny * nz;
    *out_pieces = (float **)malloc(pieces.size() * sizeof(float *));
    for (size_t i = 0; i < pieces.size(); i++) {
        (*out_pieces)[i] = (float *)malloc(n * sizeof(float));
        memcpy((*out_pieces)[i], pieces[i].data.data(), n * sizeof(float));
    }
    return 0;
}

} /* extern "C" */
