/*
 * vdbrender — Simple CPU volume path tracer for VDB files.
 *
 * Uses TinyVDB for VDB I/O and TinyEXR for EXR image output.
 * Supports density (fog) volumes and level-set surfaces.
 *
 * Licensed under the Apache License, Version 2.0.
 */
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <cfloat>
#include <algorithm>

#include "tinyvdb_io.h"

#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

/* ========================================================================== */
/*  Math                                                                      */
/* ========================================================================== */

struct Vec3 {
    float x, y, z;
    Vec3() : x(0), y(0), z(0) {}
    Vec3(float a, float b, float c) : x(a), y(b), z(c) {}
    Vec3 operator+(const Vec3 &v) const { return {x+v.x, y+v.y, z+v.z}; }
    Vec3 operator-(const Vec3 &v) const { return {x-v.x, y-v.y, z-v.z}; }
    Vec3 operator*(float s) const { return {x*s, y*s, z*s}; }
    Vec3 operator*(const Vec3 &v) const { return {x*v.x, y*v.y, z*v.z}; }
    float length() const { return sqrtf(x*x + y*y + z*z); }
    Vec3 normalized() const { float l = length(); return l > 0 ? *this * (1.0f/l) : Vec3(); }
};

static float dot(Vec3 a, Vec3 b) { return a.x*b.x + a.y*b.y + a.z*b.z; }
static Vec3 cross(Vec3 a, Vec3 b) {
    return {a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x};
}

static float clampf(float v, float lo, float hi) {
    return v < lo ? lo : (v > hi ? hi : v);
}

struct Ray { Vec3 origin, dir; };

/* Ray-AABB intersection. Returns false if no hit. */
static bool ray_box(const Ray &ray, Vec3 bmin, Vec3 bmax,
                    float &tmin_out, float &tmax_out) {
    float tmin = 0.0f, tmax = 1e30f;
    for (int i = 0; i < 3; i++) {
        float o = (&ray.origin.x)[i];
        float d = (&ray.dir.x)[i];
        float lo = (&bmin.x)[i];
        float hi = (&bmax.x)[i];
        if (fabsf(d) < 1e-20f) {
            if (o < lo || o > hi) return false;
        } else {
            float t1 = (lo - o) / d;
            float t2 = (hi - o) / d;
            if (t1 > t2) { float tmp = t1; t1 = t2; t2 = tmp; }
            tmin = std::max(tmin, t1);
            tmax = std::min(tmax, t2);
            if (tmin > tmax) return false;
        }
    }
    tmin_out = tmin;
    tmax_out = tmax;
    return true;
}

/* ========================================================================== */
/*  VDB value lookup                                                          */
/* ========================================================================== */

/* Compute the "child dimension" for each tree level — the number of index-space
   voxels each child at that level covers per axis. */
static void compute_child_dims(const tvdb_grid_layout_t *layout,
                               int child_dims[TVDB_MAX_TREE_DEPTH]) {
    for (int lv = 0; lv < layout->num_levels; lv++) {
        int dim = 1;
        for (int j = lv + 1; j < layout->num_levels; j++)
            dim *= (1 << layout->levels[j].log2dim);
        child_dims[lv] = dim;
    }
}

/* Byte popcount lookup table */
static const uint8_t popcount_table[256] = {
    0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8,
};

/* Count ON bits in a nodemask before position `pos`. */
static size_t nodemask_count_before(const tvdb_nodemask_t *mask, int32_t pos) {
    size_t count = 0;
    int32_t full_bytes = pos / 8;
    for (int32_t i = 0; i < full_bytes; i++)
        count += popcount_table[mask->bits.data[i]];
    int32_t rem = pos % 8;
    if (rem > 0)
        count += popcount_table[mask->bits.data[full_bytes] & ((1u << rem) - 1)];
    return count;
}

/* Look up a voxel value at integer index-space coordinates.
   Returns the background value if the coordinate is outside the tree. */
static float vdb_lookup(const tvdb_grid_t *grid, int ix, int iy, int iz) {
    if (grid->tree.num_nodes == 0) return 0.0f;

    const tvdb_tree_t *tree = &grid->tree;
    int child_dims[TVDB_MAX_TREE_DEPTH];
    compute_child_dims(&tree->layout, child_dims);

    const tvdb_tree_node_t *root_node = &tree->nodes[0];
    if (root_node->type != TVDB_NODE_ROOT) return 0.0f;

    const tvdb_root_node_t *root = &root_node->u.root;
    float bg = (root->background.type == TVDB_VALUE_FLOAT)
                   ? root->background.u.f : 0.0f;

    /* Find which root child contains this coordinate */
    int cdim = child_dims[0]; /* voxels per root child per axis */
    size_t child_idx = (size_t)-1;
    int32_t child_origin[3];
    for (uint32_t i = 0; i < root->num_children; i++) {
        int32_t ox = root->child_origins[i * 3 + 0];
        int32_t oy = root->child_origins[i * 3 + 1];
        int32_t oz = root->child_origins[i * 3 + 2];
        if (ix >= ox && ix < ox + cdim &&
            iy >= oy && iy < oy + cdim &&
            iz >= oz && iz < oz + cdim) {
            child_idx = root->child_indices[i];
            child_origin[0] = ox;
            child_origin[1] = oy;
            child_origin[2] = oz;
            break;
        }
    }
    if (child_idx == (size_t)-1) return bg;

    /* Traverse internal nodes */
    for (int level = 1; level < tree->layout.num_levels; level++) {
        const tvdb_tree_node_t *node = &tree->nodes[child_idx];

        if (node->type == TVDB_NODE_LEAF) {
            const tvdb_leaf_node_t *leaf = &node->u.leaf;
            int log2dim = tree->layout.levels[level].log2dim;
            int mask = (1 << log2dim) - 1;
            int lx = (ix - child_origin[0]) & mask;
            int ly = (iy - child_origin[1]) & mask;
            int lz = (iz - child_origin[2]) & mask;
            int vidx = (lz << (2 * log2dim)) | (ly << log2dim) | lx;

            if (!leaf->data || (size_t)vidx * sizeof(float) >= leaf->data_size)
                return bg;

            float val;
            memcpy(&val, leaf->data + vidx * sizeof(float), sizeof(float));
            return val;
        }

        if (node->type != TVDB_NODE_INTERNAL) return bg;

        const tvdb_internal_node_t *inode = &node->u.internal;
        int log2dim = tree->layout.levels[level].log2dim;
        int mask_dim = 1 << log2dim;
        int cdim_child = child_dims[level]; /* voxels per child of this node */

        int lx = (ix - child_origin[0]) / cdim_child;
        int ly = (iy - child_origin[1]) / cdim_child;
        int lz = (iz - child_origin[2]) / cdim_child;

        if (lx < 0 || lx >= mask_dim ||
            ly < 0 || ly >= mask_dim ||
            lz < 0 || lz >= mask_dim)
            return bg;

        int32_t slot = (int32_t)((lz << (2 * log2dim)) | (ly << log2dim) | lx);

        if (!tvdb_nodemask_is_on(&inode->child_mask, slot)) {
            /* No child — return tile/inactive value */
            if (inode->values && tvdb_nodemask_is_on(&inode->value_mask, slot)) {
                float val;
                memcpy(&val, inode->values + slot * sizeof(float),
                       sizeof(float));
                return val;
            }
            return bg;
        }

        /* Descend to child */
        size_t sparse_idx = nodemask_count_before(&inode->child_mask, slot);
        if (sparse_idx >= inode->num_children) return bg;

        child_origin[0] += lx * cdim_child;
        child_origin[1] += ly * cdim_child;
        child_origin[2] += lz * cdim_child;
        child_idx = inode->child_indices[sparse_idx];
    }

    return bg;
}

/* Sample VDB at world-space coordinates with trilinear interpolation. */
static float vdb_sample(const tvdb_grid_t *grid, float wx, float wy, float wz) {
    const tvdb_transform_t *xf = &grid->transform;

    /* World to index space */
    float fx, fy, fz;
    if (xf->type == TVDB_TRANSFORM_AFFINE) {
        /* Invert 4x4 affine matrix (Cramer's rule for 3x3 + translation) */
        const double (*m)[4] = xf->matrix;
        double det = m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
                   - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
                   + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]);
        if (fabs(det) < 1e-30) { fx = wx; fy = wy; fz = wz; }
        else {
            double inv_det = 1.0 / det;
            /* Inverse of upper-left 3x3 */
            double i00 = (m[1][1]*m[2][2]-m[1][2]*m[2][1])*inv_det;
            double i01 = (m[0][2]*m[2][1]-m[0][1]*m[2][2])*inv_det;
            double i02 = (m[0][1]*m[1][2]-m[0][2]*m[1][1])*inv_det;
            double i10 = (m[1][2]*m[2][0]-m[1][0]*m[2][2])*inv_det;
            double i11 = (m[0][0]*m[2][2]-m[0][2]*m[2][0])*inv_det;
            double i12 = (m[0][2]*m[1][0]-m[0][0]*m[1][2])*inv_det;
            double i20 = (m[1][0]*m[2][1]-m[1][1]*m[2][0])*inv_det;
            double i21 = (m[0][1]*m[2][0]-m[0][0]*m[2][1])*inv_det;
            double i22 = (m[0][0]*m[1][1]-m[0][1]*m[1][0])*inv_det;
            /* Apply: inv(M) * (w - translation) */
            double dx = (double)wx - m[0][3];
            double dy = (double)wy - m[1][3];
            double dz = (double)wz - m[2][3];
            fx = (float)(i00*dx + i01*dy + i02*dz);
            fy = (float)(i10*dx + i11*dy + i12*dz);
            fz = (float)(i20*dx + i21*dy + i22*dz);
        }
    } else {
        float vs0 = (xf->voxel_size[0] != 0.0) ? (float)xf->voxel_size[0] : 1.0f;
        float vs1 = (xf->voxel_size[1] != 0.0) ? (float)xf->voxel_size[1] : 1.0f;
        float vs2 = (xf->voxel_size[2] != 0.0) ? (float)xf->voxel_size[2] : 1.0f;
        fx = (wx - (float)xf->translation[0]) / vs0;
        fy = (wy - (float)xf->translation[1]) / vs1;
        fz = (wz - (float)xf->translation[2]) / vs2;
    }

    /* Trilinear interpolation */
    int ix = (int)floorf(fx);
    int iy = (int)floorf(fy);
    int iz = (int)floorf(fz);
    float u = fx - (float)ix;
    float v = fy - (float)iy;
    float w = fz - (float)iz;

    float c000 = vdb_lookup(grid, ix,   iy,   iz);
    float c100 = vdb_lookup(grid, ix+1, iy,   iz);
    float c010 = vdb_lookup(grid, ix,   iy+1, iz);
    float c110 = vdb_lookup(grid, ix+1, iy+1, iz);
    float c001 = vdb_lookup(grid, ix,   iy,   iz+1);
    float c101 = vdb_lookup(grid, ix+1, iy,   iz+1);
    float c011 = vdb_lookup(grid, ix,   iy+1, iz+1);
    float c111 = vdb_lookup(grid, ix+1, iy+1, iz+1);

    float c00 = c000 * (1-u) + c100 * u;
    float c10 = c010 * (1-u) + c110 * u;
    float c01 = c001 * (1-u) + c101 * u;
    float c11 = c011 * (1-u) + c111 * u;
    float c0  = c00 * (1-v) + c10 * v;
    float c1  = c01 * (1-v) + c11 * v;
    return c0 * (1-w) + c1 * w;
}

/* ========================================================================== */
/*  Bounding box computation                                                  */
/* ========================================================================== */

static void compute_world_bbox(const tvdb_grid_t *grid,
                               Vec3 &bmin, Vec3 &bmax) {
    bmin = Vec3( 1e30f,  1e30f,  1e30f);
    bmax = Vec3(-1e30f, -1e30f, -1e30f);

    if (grid->tree.num_nodes == 0) return;
    const tvdb_root_node_t *root = &grid->tree.nodes[0].u.root;
    const tvdb_transform_t *xf = &grid->transform;

    int child_dims[TVDB_MAX_TREE_DEPTH];
    compute_child_dims(&grid->tree.layout, child_dims);
    int cdim = child_dims[0];

    float vs[3] = {
        xf->voxel_size[0] != 0.0 ? (float)xf->voxel_size[0] : 1.0f,
        xf->voxel_size[1] != 0.0 ? (float)xf->voxel_size[1] : 1.0f,
        xf->voxel_size[2] != 0.0 ? (float)xf->voxel_size[2] : 1.0f,
    };
    float tr[3] = {(float)xf->translation[0], (float)xf->translation[1],
                   (float)xf->translation[2]};

    for (uint32_t i = 0; i < root->num_children; i++) {
        float lo[3], hi[3];
        for (int a = 0; a < 3; a++) {
            lo[a] = root->child_origins[i * 3 + a] * vs[a] + tr[a];
            hi[a] = (root->child_origins[i * 3 + a] + cdim) * vs[a] + tr[a];
            if (lo[a] > hi[a]) { float t = lo[a]; lo[a] = hi[a]; hi[a] = t; }
        }
        bmin.x = std::min(bmin.x, lo[0]); bmin.y = std::min(bmin.y, lo[1]);
        bmin.z = std::min(bmin.z, lo[2]);
        bmax.x = std::max(bmax.x, hi[0]); bmax.y = std::max(bmax.y, hi[1]);
        bmax.z = std::max(bmax.z, hi[2]);
    }
}

/* ========================================================================== */
/*  Rendering                                                                 */
/* ========================================================================== */

/* Temperature-based color ramp for density visualization. */
static Vec3 density_color(float d) {
    /* Black -> red -> orange -> yellow -> white */
    float r = clampf(d * 3.0f, 0.0f, 1.0f);
    float g = clampf(d * 3.0f - 1.0f, 0.0f, 1.0f);
    float b = clampf(d * 3.0f - 2.0f, 0.0f, 1.0f);
    return Vec3(r, g, b);
}

/* Render a single ray through a fog volume using emission-absorption. */
static Vec3 render_fog(const tvdb_grid_t *grid, const Ray &ray,
                       float tmin, float tmax, float step_size,
                       float density_scale) {
    Vec3 color(0, 0, 0);
    float transmittance = 1.0f;
    float t = tmin;

    while (t < tmax && transmittance > 0.001f) {
        Vec3 pos = ray.origin + ray.dir * t;
        float density = vdb_sample(grid, pos.x, pos.y, pos.z);

        if (density > 0.0f) {
            float sigma = density * density_scale;
            float dt = step_size;
            float alpha = 1.0f - expf(-sigma * dt);

            Vec3 emit = density_color(density * density_scale * 0.5f);
            color = color + emit * (alpha * transmittance);
            transmittance *= (1.0f - alpha);
        }
        t += step_size;
    }

    return color;
}

/* Estimate gradient (normal) at a point for level-set shading. */
static Vec3 estimate_gradient(const tvdb_grid_t *grid,
                              float wx, float wy, float wz, float eps) {
    float dx = vdb_sample(grid, wx + eps, wy, wz)
             - vdb_sample(grid, wx - eps, wy, wz);
    float dy = vdb_sample(grid, wx, wy + eps, wz)
             - vdb_sample(grid, wx, wy - eps, wz);
    float dz = vdb_sample(grid, wx, wy, wz + eps)
             - vdb_sample(grid, wx, wy, wz - eps);
    return Vec3(dx, dy, dz).normalized();
}

/* Render a ray against a level-set surface (find zero-crossing). */
static Vec3 render_levelset(const tvdb_grid_t *grid, const Ray &ray,
                            float tmin, float tmax, float step_size,
                            Vec3 light_dir) {
    float prev_val = vdb_sample(grid,
        ray.origin.x + ray.dir.x * tmin,
        ray.origin.y + ray.dir.y * tmin,
        ray.origin.z + ray.dir.z * tmin);
    float t = tmin + step_size;

    while (t < tmax) {
        Vec3 pos = ray.origin + ray.dir * t;
        float val = vdb_sample(grid, pos.x, pos.y, pos.z);

        /* Detect zero-crossing (outside-to-inside) */
        if (prev_val >= 0.0f && val < 0.0f) {
            /* Binary search for precise crossing */
            float t0 = t - step_size, t1 = t;
            for (int i = 0; i < 8; i++) {
                float tm = (t0 + t1) * 0.5f;
                Vec3 pm = ray.origin + ray.dir * tm;
                float vm = vdb_sample(grid, pm.x, pm.y, pm.z);
                if (vm < 0.0f) t1 = tm; else t0 = tm;
            }

            Vec3 hit = ray.origin + ray.dir * ((t0 + t1) * 0.5f);
            Vec3 normal = estimate_gradient(grid, hit.x, hit.y, hit.z,
                                            step_size * 0.5f);

            /* Simple directional + ambient shading */
            float ndotl = std::max(0.0f, dot(normal, light_dir));
            float ambient = 0.15f;
            float diffuse = 0.75f * ndotl;
            float spec_angle = std::max(0.0f,
                dot((light_dir + (ray.dir * -1.0f)).normalized(), normal));
            float specular = 0.3f * powf(spec_angle, 32.0f);

            float shade = ambient + diffuse + specular;
            return Vec3(0.8f, 0.75f, 0.7f) * shade;
        }
        prev_val = val;
        t += step_size;
    }

    return Vec3(-1, -1, -1); /* no hit sentinel */
}

/* ========================================================================== */
/*  Camera                                                                    */
/* ========================================================================== */

struct Camera {
    Vec3 eye, center, up;
    float fov_deg;
    int width, height;

    Ray generate_ray(int px, int py) const {
        float aspect = (float)width / (float)height;
        float fov_rad = fov_deg * 3.14159265f / 180.0f;
        float half_h = tanf(fov_rad * 0.5f);
        float half_w = half_h * aspect;

        float u = (2.0f * ((float)px + 0.5f) / (float)width  - 1.0f) * half_w;
        float v = (2.0f * ((float)py + 0.5f) / (float)height - 1.0f) * half_h;

        Vec3 w_dir = (center - eye).normalized();
        Vec3 u_dir = cross(w_dir, up).normalized();
        Vec3 v_dir = cross(u_dir, w_dir).normalized();

        Vec3 dir = (w_dir + u_dir * u + v_dir * v).normalized();
        return {eye, dir};
    }
};

/* ========================================================================== */
/*  Main                                                                      */
/* ========================================================================== */

static void print_usage(const char *prog) {
    fprintf(stderr,
        "Usage: %s <input.vdb> <output.exr> [options]\n"
        "\n"
        "Options:\n"
        "  --width <N>      Image width (default: 512)\n"
        "  --height <N>     Image height (default: 512)\n"
        "  --step <F>       Ray march step size in voxels (default: 0.5)\n"
        "  --density <F>    Density scale for fog volumes (default: 10.0)\n"
        "  --grid <name>    Grid name to render (default: first grid)\n"
        "  --eye <x,y,z>    Camera eye position (default: auto)\n"
        "  --fov <F>        Field of view in degrees (default: 45)\n",
        prog);
}

int main(int argc, char **argv) {
    if (argc < 3) { print_usage(argv[0]); return 1; }

    const char *infile = argv[1];
    const char *outfile = argv[2];
    int width = 512, height = 512;
    float step_voxels = 0.5f;
    float density_scale = 10.0f;
    const char *grid_name = NULL;
    float eye_x = FLT_MAX, eye_y = FLT_MAX, eye_z = FLT_MAX;
    float fov = 45.0f;

    for (int i = 3; i < argc; i++) {
        if (strcmp(argv[i], "--width") == 0 && i+1 < argc)
            width = atoi(argv[++i]);
        else if (strcmp(argv[i], "--height") == 0 && i+1 < argc)
            height = atoi(argv[++i]);
        else if (strcmp(argv[i], "--step") == 0 && i+1 < argc)
            step_voxels = (float)atof(argv[++i]);
        else if (strcmp(argv[i], "--density") == 0 && i+1 < argc)
            density_scale = (float)atof(argv[++i]);
        else if (strcmp(argv[i], "--grid") == 0 && i+1 < argc)
            grid_name = argv[++i];
        else if (strcmp(argv[i], "--eye") == 0 && i+1 < argc) {
            sscanf(argv[++i], "%f,%f,%f", &eye_x, &eye_y, &eye_z);
        } else if (strcmp(argv[i], "--fov") == 0 && i+1 < argc)
            fov = (float)atof(argv[++i]);
    }

    /* Load VDB */
    tvdb_file_t file;
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    printf("Loading %s...\n", infile);
    tvdb_status_t st = tvdb_file_open(&file, infile, NULL, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Error: %s (%s)\n", err.message,
                tvdb_status_string(st));
        return 1;
    }

    st = tvdb_read_all_grids(&file, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Error reading grids: %s\n", err.message);
        tvdb_file_close(&file);
        return 1;
    }

    /* Find the grid to render */
    size_t gi = 0;
    if (grid_name) {
        bool found = false;
        for (size_t i = 0; i < file.num_grids; i++) {
            if (strcmp(tvdb_grid_name(&file, i), grid_name) == 0) {
                gi = i; found = true; break;
            }
        }
        if (!found) {
            fprintf(stderr, "Grid '%s' not found. Available:\n", grid_name);
            for (size_t i = 0; i < file.num_grids; i++)
                fprintf(stderr, "  %s\n", tvdb_grid_name(&file, i));
            tvdb_file_close(&file);
            return 1;
        }
    }

    const tvdb_grid_t *grid = &file.grids[gi];
    printf("Rendering grid '%s' (%s)\n",
           grid->descriptor.grid_name, grid->descriptor.grid_type);

    /* Check that the grid uses a float value type */
    if (grid->tree.layout.num_levels > 0 &&
        grid->tree.layout.levels[0].value_type != TVDB_VALUE_FLOAT) {
        fprintf(stderr, "Error: only float-valued grids are supported "
                "(this grid uses %s)\n",
                grid->descriptor.grid_type);
        tvdb_file_close(&file);
        return 1;
    }

    /* Determine if level set or fog volume */
    bool is_levelset = false;
    for (size_t i = 0; i < grid->metadata.count; i++) {
        if (strcmp(grid->metadata.entries[i].name, "class") == 0 &&
            grid->metadata.entries[i].value.type == TVDB_VALUE_STRING &&
            grid->metadata.entries[i].value.u.s.str) {
            if (strstr(grid->metadata.entries[i].value.u.s.str, "level set"))
                is_levelset = true;
        }
    }
    printf("  Mode: %s\n", is_levelset ? "level set" : "fog volume");

    /* Compute bounding box */
    Vec3 bmin, bmax;
    compute_world_bbox(grid, bmin, bmax);
    Vec3 center = (bmin + bmax) * 0.5f;
    Vec3 extent = bmax - bmin;
    float max_extent = std::max({extent.x, extent.y, extent.z});

    printf("  BBox: (%.2f, %.2f, %.2f) -> (%.2f, %.2f, %.2f)\n",
           bmin.x, bmin.y, bmin.z, bmax.x, bmax.y, bmax.z);
    printf("  Extent: %.2f x %.2f x %.2f\n", extent.x, extent.y, extent.z);

    /* Step size in world space */
    float voxel_size = (float)grid->transform.voxel_size[0];
    if (voxel_size <= 0.0f) voxel_size = 1.0f;
    float step_size = voxel_size * step_voxels;

    /* Camera setup */
    Camera cam;
    cam.width = width;
    cam.height = height;
    cam.fov_deg = fov;
    cam.center = center;
    cam.up = Vec3(0, 1, 0);

    if (eye_x != FLT_MAX) {
        cam.eye = Vec3(eye_x, eye_y, eye_z);
    } else {
        /* Auto-place camera: 45-degree elevation, looking at center */
        float dist = max_extent * 1.5f;
        cam.eye = center + Vec3(dist * 0.7f, dist * 0.5f, dist * 0.7f);
    }

    printf("  Camera: eye=(%.2f, %.2f, %.2f) center=(%.2f, %.2f, %.2f)\n",
           cam.eye.x, cam.eye.y, cam.eye.z,
           cam.center.x, cam.center.y, cam.center.z);
    printf("  Image: %dx%d  Step: %.4f  Density: %.1f\n",
           width, height, step_size, density_scale);

    /* Allocate image */
    float *image = (float *)calloc((size_t)width * height * 4, sizeof(float));
    if (!image) { fprintf(stderr, "Out of memory\n"); tvdb_file_close(&file); return 1; }

    /* Light direction */
    Vec3 light_dir = Vec3(0.5f, 0.8f, 0.3f).normalized();

    /* Background gradient */
    auto background = [](float v) -> Vec3 {
        float t = clampf(v * 0.5f + 0.5f, 0.0f, 1.0f);
        Vec3 top(0.05f, 0.07f, 0.12f);
        Vec3 bot(0.15f, 0.12f, 0.10f);
        return top * t + bot * (1.0f - t);
    };

    /* Render */
    printf("Rendering...\n");
    int last_pct = -1;

    #pragma omp parallel for schedule(dynamic, 4)
    for (int py = 0; py < height; py++) {
        int pct = (py * 100) / height;
        if (pct != last_pct) {
            #pragma omp critical
            { last_pct = pct; if (pct % 10 == 0) printf("  %d%%\n", pct); }
        }

        for (int px = 0; px < width; px++) {
            Ray ray = cam.generate_ray(px, py);

            float tmin, tmax;
            Vec3 color;

            if (ray_box(ray, bmin, bmax, tmin, tmax)) {
                if (is_levelset) {
                    color = render_levelset(grid, ray, tmin, tmax,
                                            step_size, light_dir);
                    if (color.x < 0) {
                        /* No hit — use background */
                        float v = ray.dir.y;
                        color = background(v);
                    }
                } else {
                    color = render_fog(grid, ray, tmin, tmax,
                                       step_size, density_scale);
                    /* Blend with background */
                    float v = ray.dir.y;
                    Vec3 bg = background(v);
                    /* Compute remaining transmittance from color magnitude */
                    float maxc = std::max({color.x, color.y, color.z});
                    float trans = clampf(1.0f - maxc, 0.0f, 1.0f);
                    color = color + bg * trans;
                }
            } else {
                float v = ray.dir.y;
                color = background(v);
            }

            size_t idx = ((size_t)py * width + px) * 4;
            image[idx + 0] = color.x;
            image[idx + 1] = color.y;
            image[idx + 2] = color.z;
            image[idx + 3] = 1.0f;
        }
    }
    printf("  100%%\n");

    /* Write EXR */
    printf("Writing %s...\n", outfile);
    const char *exr_err = NULL;
    int ret = SaveEXR(image, width, height, 4, /*fp16=*/1, outfile, &exr_err);
    if (ret != TINYEXR_SUCCESS) {
        fprintf(stderr, "Error writing EXR: %s\n",
                exr_err ? exr_err : "unknown");
        FreeEXRErrorMessage(exr_err);
        free(image);
        tvdb_file_close(&file);
        return 1;
    }

    printf("Done.\n");
    free(image);
    tvdb_file_close(&file);
    return 0;
}
