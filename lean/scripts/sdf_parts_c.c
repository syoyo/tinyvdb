/* Differential driver for the SDF part-decomposition gate.
 *
 * Builds small deterministic dense fields (exterior shell + interior blobs,
 * some with a sealed cavity), calls the real tvdb_sdf_segmentation and
 * tvdb_sdf_extract_enclosed_regions, and prints a canonical dump:
 *
 *   case <i> conn <6|26> parts <count>
 *   field <sorted voxel indices with value < 0>
 *   part <sorted voxel indices kept by output grid c>   (one per part)
 *   cavity <sorted voxel indices with mask == 1>
 *
 * The Lean twin (Vdb/SdfPartsCheck.lean) recomputes the same partition from
 * the field line and prints the identical format; scripts/check_sdf_parts.sh
 * diffs the two files.
 *
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_mesh.h"
#include "tinyvdb_levelset.h"

#define N 6

static unsigned long long next_rand(unsigned long long *s) {
  *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17;
  return *s;
}

static void print_indices(const float *data, int n, float lo, float hi) {
  for (int i = 0; i < n; ++i)
    if (data[i] > lo && data[i] < hi) printf(" %d", i);
  printf("\n");
}

int main(void) {
  const int n = N * N * N;
  unsigned long long seed = 0x9E3779B97F4A7C15ULL;
  for (int c = 0; c < 24; ++c) {
    int conn = (c & 1) ? 26 : 6;
    tvdb_dense_grid g;
    tvdb_dense_grid_init(&g, N, N, N);
    g.voxel_size = 1.0f; g.ox = g.oy = g.oz = 0.0f;
    for (int i = 0; i < n; ++i) g.data[i] = 1.0f;

    if (c % 3 == 0) {
      /* A sealed interior shell: exterior voxels inside it are a cavity.
         Outer radius 2.2 about (2.5,2.5,2.5) stays off the forced boundary. */
      for (int k = 0; k < N; ++k)
        for (int j = 0; j < N; ++j)
          for (int i = 0; i < N; ++i) {
            double dx = i - 2.5, dy = j - 2.5, dz = k - 2.5;
            double d = sqrt(dx*dx + dy*dy + dz*dz);
            if (d >= 1.0 && d <= 2.2) g.data[(k*N + j)*N + i] = -1.0f;
          }
    } else {
      int nb = 1 + (int)(next_rand(&seed) % 3);
      for (int b = 0; b < nb; ++b) {
        double cx = 1.5 + (double)(next_rand(&seed) % 1000) / 1000.0 * 3.0;
        double cy = 1.5 + (double)(next_rand(&seed) % 1000) / 1000.0 * 3.0;
        double cz = 1.5 + (double)(next_rand(&seed) % 1000) / 1000.0 * 3.0;
        double r = 0.9 + (double)(next_rand(&seed) % 1000) / 1000.0 * 0.9;
        for (int k = 0; k < N; ++k)
          for (int j = 0; j < N; ++j)
            for (int i = 0; i < N; ++i) {
              double dx = i - cx, dy = j - cy, dz = k - cz;
              double d = sqrt(dx*dx + dy*dy + dz*dz);
              if (d <= r) g.data[(k*N + j)*N + i] = -1.0f;
            }
      }
    }
    /* Force the grid boundary exterior so cavity seeds exist. */
    for (int k = 0; k < N; ++k)
      for (int j = 0; j < N; ++j)
        for (int i = 0; i < N; ++i)
          if (i == 0 || i == N-1 || j == 0 || j == N-1 || k == 0 || k == N-1)
            g.data[(k*N + j)*N + i] = 1.0f;

    tvdb_dense_grid *parts = NULL;
    int count = 0;
    if (!tvdb_sdf_segmentation(&g, 0.0f, conn, &parts, &count)) {
      fprintf(stderr, "case %d: segmentation failed\n", c);
      return 1;
    }
    tvdb_dense_grid mask;
    if (!tvdb_sdf_extract_enclosed_regions(&g, 0.0f, conn, &mask)) {
      fprintf(stderr, "case %d: enclosed regions failed\n", c);
      return 1;
    }

    printf("case %d conn %d parts %d\n", c, conn, count);
    printf("field"); print_indices(g.data, n, -2.0f, 0.0f);
    for (int p = 0; p < count; ++p) {
      printf("part"); print_indices(parts[p].data, n, -2.0f, 0.0f);
    }
    printf("cavity"); print_indices(mask.data, n, 0.5f, 1.5f);

    for (int p = 0; p < count; ++p) tvdb_dense_grid_free(&parts[p]);
    free(parts);
    tvdb_dense_grid_free(&mask);
    tvdb_dense_grid_free(&g);
  }
  return 0;
}
