/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Differential harness: DMC-1 (Nielson dual marching cubes) TOPOLOGY (C half).
 *
 * Calls the REAL dense DMC-1 API `tvdb_sdf_to_mesh_dual_one_ex` from
 * `src/tinyvdb_mesh_dual.c` on all 256 shell-pinned sign fields of the bounded
 * n = 3 padded grid and dumps one deterministic line per field:
 *
 *   case <k> crossed <n> verts <v> quads <f> comps <c> closed <0|1> chi <int>
 *
 * The Lean twin (`Vdb/Dmc1TopologyCheck.lean`) recomputes the same six
 * invariants from the landed `Vdb.DmcOne*` model and compares them exactly.
 * Vertex indices, vertex positions and patch ids are deliberately NOT
 * compared (C patch-id allocation/ordering and QEF placement differ from
 * Lean); the banner in the twin's output names them.
 *
 * ---- Exact field convention -------------------------------------------------
 *
 * Dense grid: 4 x 4 x 4 samples (n = 3 cells), indexed
 *   linear = (z * 4 + y) * 4 + x,   x,y,z in [0,3].
 * Isovalue = 0, sample value -1.0f = "inside" (Lean `true`, case bit set),
 * +1.0f = "outside" (Lean `false`, case bit clear).
 *
 * Shell pinning (done here, before calling the non-padded DMC-1 API): a sample
 * with any coordinate in {0,3} is pinned to the OUTSIDE phase (+1.0f). The
 * eight interior samples have coordinates in {1,2}; the interior point
 *   (x,y,z) receives bit j = ((x-1)*2 + (y-1))*2 + (z-1) of k
 * (lexicographic x-slowest order, bit 0 = (1,1,1) -- exactly
 * `Vdb.DmcOnePad.fin3SignOf`). Bit set => -1.0f (inside), else +1.0f.
 *
 * We feed this already-shell-pinned 4^3 grid to `tvdb_sdf_to_mesh_dual_one_ex`
 * (NOT the `_padded_ex` variant): every sign-changing primal edge then has
 * transverse coordinates in {1,2} and hence four incident cells, so the C
 * emitter produces exactly the bounded n = 3 Lean topology.
 *
 * This driver #includes tinyvdb_mesh_dual.c so the *real* cube-local patch
 * decomposition, QEF placement and quad emitter are exercised; nothing in
 * src/ is modified. Link thread/memory/lz4/miniz support (see the gate).
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 199309L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_mesh_dual.c"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define DMC1_N 4                 /* samples per axis (n = 3 cells) */
#define DMC1_NSAMPLES (DMC1_N * DMC1_N * DMC1_N)
#define DMC1_NFIELDS 256
#define DMC1_MAX_VERTS 4096
#define DMC1_MAX_EDGES (4 * DMC1_MAX_VERTS)

/* Inside bit of the shell-pinned field at lattice point (x,y,z). */
static int dmc1_sign(int x, int y, int z, int k) {
    if (x == 0 || x == DMC1_N - 1 || y == 0 || y == DMC1_N - 1 ||
        z == 0 || z == DMC1_N - 1)
        return 0; /* shell: outside phase */
    int j = ((x - 1) * 2 + (y - 1)) * 2 + (z - 1);
    return (k >> j) & 1;
}

static void dmc1_fill(int k, float *data) {
    for (int z = 0; z < DMC1_N; ++z)
        for (int y = 0; y < DMC1_N; ++y)
            for (int x = 0; x < DMC1_N; ++x)
                data[((size_t)z * DMC1_N + y) * DMC1_N + x] =
                    dmc1_sign(x, y, z, k) ? -1.0f : 1.0f;
}

/* Number of primal lattice edges with a sign change and four incident cells,
 * computed from the sign field alone (independent of the emitted mesh).
 * An edge starts at p, runs along axis d to p+e_d (both in the lattice), and
 * has four incident cells iff each transverse coordinate of p is in {1,2}. */
static int dmc1_crossed(int k) {
    int n = 0;
    for (int z = 0; z < DMC1_N; ++z)
        for (int y = 0; y < DMC1_N; ++y)
            for (int x = 0; x < DMC1_N; ++x) {
                int p[3] = {x, y, z};
                for (int d = 0; d < 3; ++d) {
                    int q[3] = {x, y, z};
                    q[d] += 1;
                    if (q[d] > DMC1_N - 1)
                        continue; /* successor leaves the lattice */
                    int transverse_ok = 1;
                    for (int t = 0; t < 3; ++t)
                        if (t != d && (p[t] < 1 || p[t] > DMC1_N - 2))
                            transverse_ok = 0;
                    if (!transverse_ok)
                        continue; /* fewer than four incident cells */
                    if (dmc1_sign(x, y, z, k) != dmc1_sign(q[0], q[1], q[2], k))
                        ++n;
                }
            }
    return n;
}

static int dmc1_find(int parent[], int x) {
    while (parent[x] != x) {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    return x;
}

static void dmc1_union(int parent[], int a, int b) {
    int ra = dmc1_find(parent, a), rb = dmc1_find(parent, b);
    if (ra != rb)
        parent[ra] = rb;
}

static int dmc1_has_pair(const uint32_t edges[DMC1_MAX_EDGES][2], size_t n,
                         uint32_t a, uint32_t b) {
    for (size_t i = 0; i < n; ++i)
        if (edges[i][0] == a && edges[i][1] == b)
            return 1;
    return 0;
}

/* Compute verts/quads/comps/closed/chi from the REAL emitted quad mesh.
 * chi is the general V - E + F (E = distinct undirected quad sides); on a
 * closed quad mesh this equals V - F. */
static int dmc1_invariants(const tvdb_quad_mesh *m, int *verts, int *quads,
                           int *comps, int *closed, int *chi) {
    size_t V = m->vertex_count, F = m->quad_count;
    if (V > DMC1_MAX_VERTS)
        return 2;
    *verts = (int)V;
    *quads = (int)F;

    int parent[DMC1_MAX_VERTS];
    for (size_t i = 0; i < V; ++i)
        parent[i] = (int)i;

    static uint32_t de[DMC1_MAX_EDGES][2];
    static uint32_t ue[DMC1_MAX_EDGES][2];
    size_t nde = 0, nue = 0;

    for (size_t qi = 0; qi < F; ++qi) {
        const tvdb_quad *q = &m->quads[qi];
        uint32_t c[4] = {q->v0, q->v1, q->v2, q->v3};
        for (int t = 0; t < 4; ++t) {
            uint32_t a = c[t], b = c[(t + 1) & 3];
            if (a >= V || b >= V)
                return 3; /* defensive: emitted index out of range */
            if (nde >= DMC1_MAX_EDGES || nue >= DMC1_MAX_EDGES)
                return 4;
            de[nde][0] = a;
            de[nde][1] = b;
            ++nde;
            dmc1_union(parent, (int)a, (int)b);
            uint32_t lo = a < b ? a : b, hi = a < b ? b : a;
            if (!dmc1_has_pair(ue, nue, lo, hi)) {
                ue[nue][0] = lo;
                ue[nue][1] = hi;
                ++nue;
            }
        }
    }

    int ncomp = 0;
    for (size_t i = 0; i < V; ++i)
        if (dmc1_find(parent, (int)i) == (int)i)
            ++ncomp;
    *comps = ncomp;

    int cl = 1;
    for (size_t i = 0; i < nde; ++i)
        if (!dmc1_has_pair(de, nde, de[i][1], de[i][0])) {
            cl = 0;
            break;
        }
    *closed = cl;
    *chi = (int)V - (int)nue + (int)F;
    return 0;
}

int main(void) {
    printf("fields %d\n", DMC1_NFIELDS);
    float data[DMC1_NSAMPLES];
    for (int k = 0; k < DMC1_NFIELDS; ++k) {
        dmc1_fill(k, data);
        tvdb_dense_grid g = {DMC1_N, DMC1_N, DMC1_N, 0.0f, 0.0f, 0.0f, 1.0f, data};
        tvdb_quad_mesh m;
        tvdb_quad_mesh_init(&m);
        tvdb_error_t err = {0};
        tvdb_status_t st = tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, NULL, &m, NULL, &err);
        if (st != TVDB_OK) {
            fprintf(stderr, "tvdb_sdf_to_mesh_dual_one_ex failed: case=%d status=%d msg=%s\n",
                    k, (int)st, err.message);
            tvdb_quad_mesh_free(&m);
            return 1;
        }

        int crossed = dmc1_crossed(k);
        int verts = 0, quads = 0, comps = 0, closed = 0, chi = 0;
        int rc = dmc1_invariants(&m, &verts, &quads, &comps, &closed, &chi);
        if (rc != 0) {
            fprintf(stderr, "invariant computation failed: case=%d rc=%d\n", k, rc);
            tvdb_quad_mesh_free(&m);
            return 2;
        }
        /* The C emitter emits one quad per crossed primal edge with four
         * incident cells; the independent sign-field count must agree. */
        if (crossed != quads) {
            fprintf(stderr, "crossed/quad mismatch: case=%d crossed=%d quads=%d\n",
                    k, crossed, quads);
            tvdb_quad_mesh_free(&m);
            return 3;
        }

        printf("case %d crossed %d verts %d quads %d comps %d closed %d chi %d\n",
               k, crossed, verts, quads, comps, closed, chi);
        tvdb_quad_mesh_free(&m);
    }
    return 0;
}
