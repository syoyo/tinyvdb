// Finding F11: the dense mesh->SDF sign used the closest face's normal,
// which misclassifies points near sharp edges/vertices even for convex
// meshes (the sign then depends on an arbitrary tie-break between the two
// faces sharing the edge).
//
// Confirmed counterexample (2026-11-14): outward-oriented tetrahedron
//   A=(0,0,3), B=(-2,-2,0), C=(2,-2,0), D=(0,2,0).
// The closest feature for outside points along the A-D edge is the edge
// itself; d . n_ACD < 0 < d . n_ADB, so whichever face the BVH tie-break
// picks decides the sign. With pseudo-normals (sum of the adjacent face
// normals) the sign is correct.
//
// This test builds all cells strictly below the surface (inside, v < 0) and
// strictly above it (outside, v > 0) of the tetrahedron, using plane-
// halfspace tests with a safety margin, and requires the dense SDF to agree
// everywhere. Voxel centers are used as query points (as in the real path).

#include "tinyvdb_io.h"
#include "tinyvdb_mesh.h"
#include "tinyvdb_mesh_conversion.h"
#include "tinyvdb_thread.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static tvdb_vec3f T_A = {0.0f, 0.0f, 3.0f};
static tvdb_vec3f T_B = {-2.0f, -2.0f, 0.0f};
static tvdb_vec3f T_C = {2.0f, -2.0f, 0.0f};
static tvdb_vec3f T_D = {0.0f, 2.0f, 0.0f};

/* Outward normals (verified: cross products match vertex order). */
static tvdb_vec3f cross3(tvdb_vec3f a, tvdb_vec3f b) {
    return (tvdb_vec3f){a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x};
}
static tvdb_vec3f sub3(tvdb_vec3f a, tvdb_vec3f b) {
    return (tvdb_vec3f){a.x - b.x, a.y - b.y, a.z - b.z};
}
static float dot3(tvdb_vec3f a, tvdb_vec3f b) {
    return a.x * b.x + a.y * b.y + a.z * b.z;
}
static tvdb_vec3f face_normal(tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c) {
    tvdb_vec3f n = cross3(sub3(b, a), sub3(c, a));
    float len = sqrtf(dot3(n, n));
    return (tvdb_vec3f){n.x / len, n.y / len, n.z / len};
}

/* Signed distance to each of the 4 face planes (positive = outside). */
static void plane_values(tvdb_vec3f p, float out[4]) {
    tvdb_vec3f n0 = face_normal(T_A, T_B, T_C);
    tvdb_vec3f n1 = face_normal(T_A, T_C, T_D);
    tvdb_vec3f n2 = face_normal(T_A, T_D, T_B);
    tvdb_vec3f n3 = face_normal(T_B, T_D, T_C);
    out[0] = dot3(sub3(p, T_A), n0);
    out[1] = dot3(sub3(p, T_A), n1);
    out[2] = dot3(sub3(p, T_A), n2);
    out[3] = dot3(sub3(p, T_B), n3);
}

int main(void) {
    tvdb_triangle faces[4] = {{0, 1, 2}, {0, 2, 3}, {0, 3, 1}, {1, 3, 2}};
    tvdb_vec3f verts[4] = {T_A, T_B, T_C, T_D};
    tvdb_triangle_mesh mesh = {verts, 4, 4, faces, 4, 4};

    float h = 0.2f;
    float low[3] = {-2.5f, -2.5f, -0.5f};
    int dim[3] = {25, 25, 20}; /* covers the tetrahedron with a small margin */
    tvdb_thread_pool_t *pool = NULL;
    if (tvdb_thread_pool_create(1, &pool, NULL) != TVDB_OK) {
        fprintf(stderr, "FAIL: pool\n");
        return 1;
    }

    tvdb_dense_grid g = {0};
    if (tvdb_mesh_to_sdf_ex(&mesh, h, 0.75f, pool, &g, NULL, NULL) != TVDB_OK) {
        fprintf(stderr, "FAIL: tvdb_mesh_to_sdf_ex\n");
        tvdb_thread_pool_destroy(pool);
        return 1;
    }

    int bad_outside = 0, bad_inside = 0, checked = 0;
    for (int z = 0; z < g.nz; ++z)
        for (int y = 0; y < g.ny; ++y)
            for (int x = 0; x < g.nx; ++x) {
                tvdb_vec3f p = {g.ox + (x + 0.5f) * h, g.oy + (y + 0.5f) * h,
                                g.oz + (z + 0.5f) * h};
                float pv[4];
                plane_values(p, pv);
                float v = g.data[((size_t)z * g.ny + y) * g.nx + x];
                int in_count = 0, out_count = 0;
                for (int i = 0; i < 4; ++i) {
                    if (pv[i] < -0.05f) ++in_count;  /* strictly inside plane i */
                    if (pv[i] > 0.05f) ++out_count;  /* strictly outside plane i */
                }
                int outside = out_count > 0;     /* beyond at least one plane */
                int inside = in_count == 4;      /* inside all four planes */
                if (outside) {
                    /* Strictly outside the tetrahedron: SDF must be >= 0. */
                    if (++checked, v < 0.0f) {
                        if (bad_outside++ < 5)
                            fprintf(stderr,
                                    "outside voxel (%d,%d,%d) p=(%.2f,%.2f,%.2f) v=%g\n",
                                    x, y, z, p.x, p.y, p.z, v);
                    }
                } else if (inside) {
                    /* Strictly inside the tetrahedron: SDF must be <= 0. */
                    if (++checked, v > 0.0f) {
                        if (bad_inside++ < 5)
                            fprintf(stderr,
                                    "inside voxel (%d,%d,%d) p=(%.2f,%.2f,%.2f) v=%g\n",
                                    x, y, z, p.x, p.y, p.z, v);
                    }
                }
            }

    tvdb_dense_grid_free(&g);
    tvdb_thread_pool_destroy(pool);

    if (bad_outside || bad_inside) {
        fprintf(stderr, "FAIL: %d outside voxels negative, %d inside voxels positive (checked %d)\n",
                bad_outside, bad_inside, checked);
        return 1;
    }
    printf("test_mesh_pseudo_normal: ok (%d voxels checked)\n", checked);
    return 0;
}
