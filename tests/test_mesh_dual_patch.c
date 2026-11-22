/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Cube-local MC patch decomposition (DMC-1 first slice).
 *
 * Independent oracle: the triangle soup is re-read from the shipped MC table
 * and its connected components are counted by adjacency BFS (not by the
 * union-find used in the library). The patch-count distribution, the exact
 * 3-/4-patch case lists, and the per-edge patch ownership mirror the
 * machine-checked facts in Lean's Vdb.DmcOne. No dual-mesh output is
 * touched: this only exercises the pure, allocation-free patch helper. */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "tinyvdb_mc_tri_table.h"
#include "tinyvdb_mesh_dual.h"

#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "line %d: %s\n", __LINE__, #x);                                        \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)

/* Same edge -> corner table as the C MC table and Lean McTable.mcEdgeVerts. */
static const int EDGE[12][2] = {{0, 1}, {1, 2}, {2, 3}, {3, 0},
                                {4, 5}, {5, 6}, {6, 7}, {7, 4},
                                {0, 4}, {1, 5}, {2, 6}, {3, 7}};

/* Read the case's soup into triples; return the triangle count (0..5). */
static int soup(unsigned k, int tris[5][3]) {
    const int *row = MC_TRI_TABLE[k];
    int n = 0;
    for (int i = 0; i + 2 < 16 && n < 5; i += 3) {
        if (row[i] < 0)
            break;
        tris[n][0] = row[i];
        tris[n][1] = row[i + 1];
        tris[n][2] = row[i + 2];
        ++n;
    }
    return n;
}

/* Independent component count: adjacency flood-fill over the used cube edges. */
static int ref_patch_count(unsigned k) {
    int tris[5][3];
    int n = soup(k, tris);
    bool adj[12][12], used[12], seen[12];
    memset(adj, 0, sizeof(adj));
    memset(used, 0, sizeof(used));
    memset(seen, 0, sizeof(seen));
    for (int t = 0; t < n; ++t) {
        const int *v = tris[t];
        used[v[0]] = used[v[1]] = used[v[2]] = true;
        const int pairs[3][2] = {{0, 1}, {1, 2}, {0, 2}};
        for (int p = 0; p < 3; ++p) {
            int a = v[pairs[p][0]], b = v[pairs[p][1]];
            adj[a][b] = adj[b][a] = true;
        }
    }
    int stack[12], comps = 0;
    for (int e = 0; e < 12; ++e) {
        if (!used[e] || seen[e])
            continue;
        ++comps;
        int top = 0;
        stack[top++] = e;
        seen[e] = true;
        while (top) {
            int u = stack[--top];
            for (int w = 0; w < 12; ++w)
                if (adj[u][w] && !seen[w]) {
                    seen[w] = true;
                    stack[top++] = w;
                }
        }
    }
    return comps;
}

/* Bitmask of cube edges occurring in the case's soup. */
static uint16_t soup_mask(unsigned k) {
    int tris[5][3];
    int n = soup(k, tris);
    uint16_t m = 0;
    for (int t = 0; t < n; ++t)
        for (int j = 0; j < 3; ++j)
            m |= (uint16_t)(1u << tris[t][j]);
    return m;
}

/* Bitmask of sign-changing edges from the case's corner bits. */
static uint16_t sign_mask(unsigned k) {
    uint16_t m = 0;
    for (int e = 0; e < 12; ++e) {
        unsigned a = (k >> EDGE[e][0]) & 1u, b = (k >> EDGE[e][1]) & 1u;
        if (a != b)
            m |= (uint16_t)(1u << e);
    }
    return m;
}

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;

    int dist[5] = {0, 0, 0, 0, 0};
    int threes[16], nthree = 0, fours[8], nfour = 0;
    const int want_three[] = {26, 37, 74, 82, 88, 133, 161, 164};
    const int want_four[] = {90, 165};

    for (unsigned k = 0; k < 256; ++k) {
        tvdb_dual_patch_info info;
        CHECK(tvdb_dual_patch_compute(k, &info));

        int tris[5][3];
        int n = soup(k, tris);
        int pc = ref_patch_count(k);

        CHECK(info.tri_count == n);
        CHECK(info.patch_count == pc);
        CHECK(info.patch_count <= TVDB_DUAL_PATCH_MAX_PATCHES);
        CHECK((info.patch_count == 0) == (n == 0));
        /* The soup's edges are exactly the sign-changing edges (T-MC-EDGE /
         * T-MC-COMPLETE / T-MC-NO-INVENT), and the reported mask agrees. */
        CHECK(info.cross_mask == soup_mask(k));
        CHECK(info.cross_mask == sign_mask(k));

        /* Distinct triangle patch ids = patch count; ids are in range. */
        int seen_patch[TVDB_DUAL_PATCH_MAX_PATCHES];
        int nseen = 0;
        for (int t = 0; t < n; ++t) {
            int p = info.tri_patch[t];
            CHECK(p < info.patch_count);
            bool found = false;
            for (int j = 0; j < nseen; ++j)
                if (seen_patch[j] == p)
                    found = true;
            if (!found)
                seen_patch[nseen++] = p;
        }
        CHECK(nseen == info.patch_count);

        /* Per-edge ownership: at most one patch per edge, and exactly one
         * for every sign-changing edge. Recompute the owner from the soup. */
        for (int e = 0; e < 12; ++e) {
            int owners[TVDB_DUAL_PATCH_MAX_PATCHES], nowners = 0;
            for (int t = 0; t < n; ++t) {
                if (tris[t][0] != e && tris[t][1] != e && tris[t][2] != e)
                    continue;
                int p = info.tri_patch[t];
                bool found = false;
                for (int j = 0; j < nowners; ++j)
                    if (owners[j] == p)
                        found = true;
                if (!found)
                    owners[nowners++] = p;
            }
            CHECK(info.edge_patch_count[e] == nowners);
            CHECK(nowners <= 1);
            CHECK(nowners == (int)((info.cross_mask >> e) & 1u));
            for (int j = 0; j < nowners; ++j)
                CHECK(info.edge_patch[e][j] == owners[j]);
        }

        dist[info.patch_count < 5 ? info.patch_count : 4]++;
        if (info.patch_count == 3) {
            CHECK(nthree < 16);
            threes[nthree++] = (int)k;
        }
        if (info.patch_count == 4) {
            CHECK(nfour < 8);
            fours[nfour++] = (int)k;
        }
    }

    CHECK(dist[0] == 2 && dist[1] == 162 && dist[2] == 82 && dist[3] == 8 && dist[4] == 2);
    CHECK(nthree == 8 && nfour == 2);
    for (int i = 0; i < 8; ++i)
        CHECK(threes[i] == want_three[i]);
    for (int i = 0; i < 2; ++i)
        CHECK(fours[i] == want_four[i]);

    /* Invalid inputs are rejected without touching the output struct. */
    tvdb_dual_patch_info sentinel;
    memset(&sentinel, 0xa5, sizeof(sentinel));
    tvdb_dual_patch_info copy = sentinel;
    CHECK(!tvdb_dual_patch_compute(256, &copy));
    CHECK(memcmp(&copy, &sentinel, sizeof(copy)) == 0);
    CHECK(!tvdb_dual_patch_compute(0, NULL));

    puts("test_mesh_dual_patch: OK (256 cases, patch decomposition parity)");
    return 0;
}
