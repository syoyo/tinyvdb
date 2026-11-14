// Finding F16: the unweighted vertex pseudo-normal sign rule is unsound,
// even for convex meshes.
//
// Machine-checked counterexample (2026-11-14, lean/Vdb/PseudoNormal.lean):
// the rational-coordinate tetrahedron with apex at the origin and base
// z = -1 (vertices A=(0,0,0), V12=(0,1/2,-1), V13=(0,-1/2,-1), V23=(-1/2,0,-1))
// has unit outward normals n1=(1,0,0), n2=(-2/3,2/3,1/3), n3=(-2/3,-2/3,1/3) at
// the apex. For p = t*n1 (t > 0) the outside point violates the face-1
// halfspace, and its closest point is the apex. The unweighted pseudo-normal
// nu = n1 + n2 + n3 = (-1/3, 0, 2/3) pairs negatively with p - A
// (<nu, p - A> = -t/3 < 0), so the old sign rule classified the outside point
// as inside (reproduced end-to-end: the generated dense grid assigned
// v = -0.166 at an outside voxel, closest feature correct, sign wrong).
//
// Fix: vertex features now take the maximum dot product over incident faces'
// outward normals; an outside point of a convex polyhedron pairs positively
// with at least one incident face, an inside point with none. This test
// asserts the sign on every cell of the tetrahedron with a halfspace margin
// (mirroring test_mesh_pseudo_normal.c).

#include "tinyvdb_io.h"
#include "tinyvdb_mesh.h"
#include "tinyvdb_mesh_conversion.h"
#include "tinyvdb_thread.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static tvdb_vec3f T_A = {0.0f, 0.0f, 0.0f};
static tvdb_vec3f T_V12 = {0.0f, 0.5f, -1.0f};
static tvdb_vec3f T_V13 = {0.0f, -0.5f, -1.0f};
static tvdb_vec3f T_V23 = {-0.5f, 0.0f, -1.0f};

/* Signed distance to each of the 4 face planes (positive = outside). */
static void plane_values(tvdb_vec3f p, float out[4]) {
    out[0] = p.x - T_A.x;
    out[1] = ((-2.0f * (p.x - T_A.x) + 2.0f * (p.y - T_A.y) + (p.z - T_A.z))) / 3.0f;
    out[2] = ((-2.0f * (p.x - T_A.x) - 2.0f * (p.y - T_A.y) + (p.z - T_A.z))) / 3.0f;
    out[3] = -(p.z - T_V12.z);
}

int main(void) {
    /* Outward winding (cross products verified to point outward):
     * face 1: (A, V13, V12), face 2: (A, V12, V23),
     * face 3: (A, V23, V13), face 4 (base): (V12, V13, V23). */
    tvdb_triangle faces[4] = {{0, 2, 1}, {0, 1, 3}, {0, 3, 2}, {1, 2, 3}};
    tvdb_vec3f verts[4] = {T_A, T_V12, T_V13, T_V23};
    tvdb_triangle_mesh mesh = {verts, 4, 4, faces, 4, 4};

    float h = 0.1f;
    tvdb_thread_pool_t *pool = NULL;
    if (tvdb_thread_pool_create(1, &pool, NULL) != TVDB_OK) {
        fprintf(stderr, "FAIL: pool\n");
        return 1;
    }

    tvdb_dense_grid g = {0};
    if (tvdb_mesh_to_sdf_ex(&mesh, h, 0.25f, pool, &g, NULL, NULL) != TVDB_OK) {
        fprintf(stderr, "FAIL: tvdb_mesh_to_sdf_ex\n");
        tvdb_thread_pool_destroy(pool);
        return 1;
    }

    int bad_outside = 0, bad_inside = 0, checked = 0, vertex_outside = 0;
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
                int outside = out_count > 0;
                int inside = in_count == 4;
                if (outside) {
                    /* Strictly outside: SDF must be >= 0. */
                    if (++checked, v < 0.0f) {
                        if (bad_outside++ < 5)
                            fprintf(stderr,
                                    "outside voxel (%d,%d,%d) p=(%.2f,%.2f,%.2f) v=%g\n",
                                    x, y, z, p.x, p.y, p.z, v);
                    }
                } else if (inside) {
                    /* Strictly inside: SDF must be <= 0. */
                    if (++checked, v > 0.0f) {
                        if (bad_inside++ < 5)
                            fprintf(stderr,
                                    "inside voxel (%d,%d,%d) p=(%.2f,%.2f,%.2f) v=%g\n",
                                    x, y, z, p.x, p.y, p.z, v);
                    }
                }
            }
    /* Count voxels outside along the face-1 axis to show the check has teeth. */
    for (int z = 0; z < g.nz; ++z)
        for (int y = 0; y < g.ny; ++y)
            for (int x = 0; x < g.nx; ++x) {
                float px = g.ox + (x + 0.5f) * h;
                if (px > 0.05f) ++vertex_outside;
            }

    tvdb_dense_grid_free(&g);
    tvdb_thread_pool_destroy(pool);

    if (bad_outside || bad_inside) {
        fprintf(stderr, "FAIL: %d outside voxels negative, %d inside voxels positive (checked %d)\n",
                bad_outside, bad_inside, checked);
        return 1;
    }
    if (vertex_outside == 0) {
        fprintf(stderr, "FAIL: no outside voxels beyond face 1 -- the test has no teeth\n");
        return 1;
    }
    printf("test_mesh_vertex_sign: ok (%d voxels checked, %d outside face 1)\n", checked,
           vertex_outside);
    return 0;
}
