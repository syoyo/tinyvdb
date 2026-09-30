/* CPU-parity for the index-map paths, on both backends.
 *
 * TVDB_INDEX_MAP_MIN_ACTIVE is 2048, so the 44-case suite's 64-voxel active set
 * takes the linear-scan path on both backends and never reaches the map. The
 * map replaces a linear scan with a host-built open-addressing table, so it has
 * to be correct on its own terms and nothing else in the suite checks it:
 *
 *   - first-seen semantics. `values` stores first_seen_index + 1 with 0 meaning
 *     "empty", and the host inserts in increasing active-index order so the
 *     first insert into a slot wins. A query for a duplicated coordinate must
 *     therefore return the *earliest* active index, not an arbitrary one. The
 *     active set below deliberately contains duplicates.
 *   - misses. A coordinate absent from the active set must return -1 / 0, which
 *     is the case the probe loop's early "empty slot" exit handles.
 *   - signed coordinates, including INT32_MIN-adjacent values, since the hash is
 *     computed on the bit pattern.
 *   - both connectivities, and the size both just under and well over the gate,
 *     so the crossover itself is covered.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"
#include "tinyvdb_grid_index.h"

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
  fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); ++g_failures; } } while (0)

/* Deterministic, with duplicates injected so first-seen ordering is observable. */
static uint32_t rng_state = 2166136261u;
static uint32_t rng(void) {
  rng_state ^= rng_state << 13; rng_state ^= rng_state >> 17; rng_state ^= rng_state << 5;
  return rng_state;
}

static void build_case(int L, int32_t* active, size_t* out_na, int dup_every) {
  size_t na = 0;
  size_t cap = (size_t)L * L * L * 2u;
  for (int z = 0; z < L; ++z)
    for (int y = 0; y < L; ++y)
      for (int x = 0; x < L; ++x) {
        if (((x + 3 * y + 5 * z) % 3) != 0) continue;   /* ~1/3 active */
        /* Bias towards negative coordinates so the sign path is used. */
        int32_t ax = (int32_t)x - L / 2, ay = (int32_t)y - L / 3, az = (int32_t)z - L / 4;
        active[3 * na + 0] = ax; active[3 * na + 1] = ay; active[3 * na + 2] = az;
        ++na;
        if (dup_every && (na % (size_t)dup_every) == 0 && na < cap) {
          /* Re-insert the same coordinate later: a correct map must still report
           * the first occurrence for any query on it. */
          active[3 * na + 0] = ax; active[3 * na + 1] = ay; active[3 * na + 2] = az;
          ++na;
        }
      }
  *out_na = na;
}

static void run_case(tvdb_gpu_context_t* ctx, int L, const char* note) {
  size_t cap = (size_t)L * L * L * 2u;
  int32_t* active = (int32_t*)malloc(cap * 3 * sizeof(int32_t));
  size_t na = 0;
  build_case(L, active, &na, 7);
  /* This test exists to cover the map path, so it is worthless below the gate. */
  if (na < 2048) {
    printf("  FAIL %-22s na=%zu is below TVDB_INDEX_MAP_MIN_ACTIVE (2048): "
           "this case is testing the linear scan, not the map. Raise L.\n", note, na);
    ++g_failures;
  }

  /* Queries: every active coordinate (must hit, first-seen index), plus a
   * deterministic mix of misses, including far out-of-range ones. */
  const size_t nq = na + 4096;
  int32_t* query = (int32_t*)malloc(nq * 3 * sizeof(int32_t));
  memcpy(query, active, na * 3 * sizeof(int32_t));
  for (size_t i = na; i < nq; ++i) {
    uint32_t r = rng();
    if (r & 1u) { query[3*i+0] = (int32_t)(r >> 3); query[3*i+1] = (int32_t)(r >> 13); query[3*i+2] = (int32_t)(r >> 21); }
    else { query[3*i+0] = -((int32_t)L) - 1 - (int32_t)(r % 7u);
           query[3*i+1] =  (int32_t)L + 1 + (int32_t)(r % 5u);
           query[3*i+2] = -(int32_t)(r % 3u); }
  }

  int64_t* cpu_idx = (int64_t*)malloc(nq * sizeof(int64_t));
  int64_t* gpu_idx = (int64_t*)malloc(nq * sizeof(int64_t));
  EXPECT(tvdb_ijk_to_index(active, na, query, nq, cpu_idx));
  tvdb_error_t e; memset(&e, 0, sizeof e);
  if (tvdb_gpu_ijk_to_index(ctx, active, na, query, nq, gpu_idx, &e) != TVDB_OK) {
    printf("  FAIL %-22s ijk_to_index: %s\n", note, e.message);
    ++g_failures;
  } else {
    size_t bad = 0; size_t first = 0;
    for (size_t i = 0; i < nq; ++i)
      if (cpu_idx[i] != gpu_idx[i]) { if (!bad) first = i; ++bad; }
    if (bad) { printf("  FAIL %-22s ijk_to_index %zu/%zu differ, first at %zu (cpu %lld gpu %lld)\n",
                      note, bad, nq, first, (long long)cpu_idx[first], (long long)gpu_idx[first]); ++g_failures; }
    else printf("  ok   %-22s ijk_to_index  na=%zu nq=%zu exact\n", note, na, nq);
  }

  /* points_in_grid: voxel centres of every query, so hits map back to the same
   * first-seen index and the misses must report 0. */
  const float vs[3] = { 0.5f, 0.5f, 0.5f };
  const float origin[3] = { -3.25f, 7.5f, -1.75f };
  float* points = (float*)malloc(nq * 3 * sizeof(float));
  for (size_t i = 0; i < nq; ++i) {
    points[3*i+0] = origin[0] + ((float)query[3*i+0] + 0.5f) * vs[0];
    points[3*i+1] = origin[1] + ((float)query[3*i+1] + 0.5f) * vs[1];
    points[3*i+2] = origin[2] + ((float)query[3*i+2] + 0.5f) * vs[2];
  }
  uint8_t* cpu_pm = (uint8_t*)malloc(nq);
  uint8_t* gpu_pm = (uint8_t*)malloc(nq);
  EXPECT(tvdb_points_in_set(points, nq, vs, origin, active, na, cpu_pm));
  if (tvdb_gpu_points_in_grid(ctx, points, nq, vs, origin, active, na, gpu_pm, &e) != TVDB_OK) {
    printf("  FAIL %-22s points_in_grid: %s\n", note, e.message);
    ++g_failures;
  } else {
    size_t bad = 0;
    for (size_t i = 0; i < nq; ++i) if (cpu_pm[i] != gpu_pm[i]) ++bad;
    if (bad) { printf("  FAIL %-22s points_in_grid %zu/%zu differ\n", note, bad, nq); ++g_failures; }
    else printf("  ok   %-22s points_in_grid na=%zu nq=%zu exact\n", note, na, nq);
  }

  int32_t* cpu_nc = (int32_t*)malloc(na * sizeof(int32_t));
  int32_t* gpu_nc = (int32_t*)malloc(na * sizeof(int32_t));
  for (int conn = 6; conn <= 26; conn += 20) {
    EXPECT(tvdb_neighbor_counts(active, na, conn, cpu_nc));
    if (tvdb_gpu_neighbor_counts(ctx, active, na, conn, gpu_nc, &e) != TVDB_OK) {
      printf("  FAIL %-22s neighbor_counts(%d): %s\n", note, conn, e.message);
      ++g_failures;
    } else {
      size_t bad = 0; size_t first = 0;
      for (size_t i = 0; i < na; ++i) if (cpu_nc[i] != gpu_nc[i]) { if (!bad) first = i; ++bad; }
      if (bad) { printf("  FAIL %-22s neighbor_counts(%d) %zu/%zu differ, first at %zu (cpu %d gpu %d)\n",
                        note, conn, bad, na, first, cpu_nc[first], gpu_nc[first]); ++g_failures; }
      else printf("  ok   %-22s neighbor_counts(conn=%2d) na=%zu exact\n", note, conn, na);
    }
  }

  free(active); free(query); free(cpu_idx); free(gpu_idx); free(points);
  free(cpu_pm); free(gpu_pm); free(cpu_nc); free(gpu_nc);
}

/* Sparse convolution over a grid whose bounding box is too large for a dense
 * index grid (tvdb_sparse_bbox gives up above 4e8 voxels), which is the only way
 * to reach the map-probed conv path at all -- and on CUDA it is the *only* way,
 * so without this case the CUDA map conv would be unreachable code.
 *
 * This is also the case the path exists for: a few thousand voxels scattered
 * through a billion-voxel volume. The brute-force alternative does a full scan
 * of the active set for every one of the 27 taps. */
static void run_sparse_conv(tvdb_gpu_context_t* ctx) {
  const size_t count = 3000;
  const int span = 1100;                 /* span^3 = 1.33e9 > 4e8 */
  tvdb_sparse_grid in; memset(&in, 0, sizeof in);
  in.coords = (tvdb_vec3i*)malloc(count * sizeof(tvdb_vec3i));
  in.values = (float*)malloc(count * sizeof(float));
  in.capacity = count; in.count = count; in.voxel_size = 1.0f;
  for (size_t i = 0; i < count; ++i) {
    in.coords[i].x = (int32_t)(rng() % (uint32_t)span) - span / 2;
    in.coords[i].y = (int32_t)(rng() % (uint32_t)span) - span / 2;
    in.coords[i].z = (int32_t)(rng() % (uint32_t)span) - span / 2;
    in.values[i] = 1.0f + 0.5f * (float)(i % 11);
  }
  /* Guarantee a few exact duplicates: the map must report the first-seen voxel
   * value, exactly as the brute-force kernel's "first match wins" scan did. */
  for (size_t i = 1; i < 64; ++i) { in.coords[i] = in.coords[0]; in.values[i] = 99.0f; }

  float kern[27];
  for (int i = 0; i < 27; ++i) kern[i] = 0.1f * (float)(i % 5);
  const float pad = 0.25f;

  tvdb_sparse_grid cpu; memset(&cpu, 0, sizeof cpu);
  tvdb_error_t e; memset(&e, 0, sizeof e);
  /* The CPU reference returns bool, not a status. */
  if (!tvdb_sparse_conv3d(&in, kern, 3, 3, 3, pad, &cpu)) {
    printf("  FAIL %-22s cpu reference failed\n", "sparse-conv-map");
    ++g_failures;
  } else {
    tvdb_sparse_grid gpu; memset(&gpu, 0, sizeof gpu);
    if (tvdb_gpu_sparse_conv3d(ctx, &in, kern, 3, 3, 3, pad, &gpu, &e) != TVDB_OK) {
      printf("  FAIL %-22s %s\n", "sparse-conv-map", e.message);
      ++g_failures;
    } else if (gpu.count != cpu.count) {
      printf("  FAIL %-22s count %zu vs %zu\n", "sparse-conv-map", gpu.count, cpu.count);
      ++g_failures;
    } else {
      double worst = 0.0; size_t wi = 0;
      for (size_t i = 0; i < cpu.count; ++i) {
        if (cpu.coords[i].x != gpu.coords[i].x || cpu.coords[i].y != gpu.coords[i].y ||
            cpu.coords[i].z != gpu.coords[i].z) {
          printf("  FAIL %-22s coord %zu differs\n", "sparse-conv-map", i); ++g_failures; break;
        }
        double d = fabs((double)cpu.values[i] - (double)gpu.values[i]);
        double sc = fabs((double)cpu.values[i]) > 1e-6 ? fabs((double)cpu.values[i]) : 1.0;
        if (d / sc > worst) { worst = d / sc; wi = i; }
      }
      if (worst > 1e-5) {
        printf("  FAIL %-22s worst rel %.3e at %zu (cpu %g gpu %g)\n",
               "sparse-conv-map", worst, wi, cpu.values[wi], gpu.values[wi]);
        ++g_failures;
      } else {
        printf("  ok   %-22s count=%zu worst rel %.3e (bbox %d^3 over dense limit)\n",
               "sparse-conv-map", cpu.count, worst, span);
      }
    }
    tvdb_sparse_grid_free(&cpu);
  }
  free(in.coords); free(in.values);
}

/* The reusable-map path: build once, query many. Compared against the CPU and
 * against the per-call path, on both backends.
 *
 * The point of the reusable form is that it is the same computation with the map
 * build and upload hoisted out, so the checks that matter are (a) it agrees with
 * the CPU, (b) it agrees with the per-call path it replaces, and (c) repeated
 * queries do not drift -- the map is device-resident state, so a stale or aliased
 * buffer would show up as the third or fourth query disagreeing rather than the
 * first. Interleaving the query kinds is deliberate for the same reason: they
 * share two descriptor sets and must not trample each other's bindings. */
static void run_reusable(tvdb_gpu_context_t* ctx, int L, const char* note) {
  size_t cap = (size_t)L * L * L * 2u;
  int32_t* active = (int32_t*)malloc(cap * 3 * sizeof(int32_t));
  size_t na = 0;
  build_case(L, active, &na, 7);
  if (na < 2048) { printf("  FAIL %-22s na=%zu below the map gate\n", note, na); ++g_failures; goto done; }

  /* Several distinct query batches, so a map that got corrupted after the first
   * use, or scratch that aliases between kinds, is caught. */
  enum { NB = 4 };
  const size_t nq = 8192;
  int32_t* q[NB]; size_t nqh[NB];
  for (int b = 0; b < NB; ++b) {
    nqh[b] = nq + (size_t)b * 997;      /* deliberately different sizes */
    q[b] = (int32_t*)malloc(nqh[b] * 3 * sizeof(int32_t));
    for (size_t i = 0; i < nqh[b]; ++i) {
      uint32_t r = rng();
      if (r & 1u) { size_t k = (r >> 8) % na;
        q[b][3*i+0] = active[3*k+0]; q[b][3*i+1] = active[3*k+1]; q[b][3*i+2] = active[3*k+2]; }
      else { q[b][3*i+0] = (int32_t)(r >> 3); q[b][3*i+1] = (int32_t)(r >> 13); q[b][3*i+2] = (int32_t)(r >> 21); }
    }
  }
  int32_t* ncpu = (int32_t*)malloc(na * sizeof(int32_t));
  int32_t* ngpu = (int32_t*)malloc(na * sizeof(int32_t));

  tvdb_gpu_index_map_t* map = NULL;
  tvdb_error_t e; memset(&e, 0, sizeof e);
  if (tvdb_gpu_index_map_create(ctx, active, na, &map, &e) != TVDB_OK) {
    printf("  FAIL %-22s index_map_create: %s\n", note, e.message); ++g_failures;
    goto done;
  }
  if (tvdb_gpu_index_map_active_count(map) != na) {
    printf("  FAIL %-22s active_count %zu != %zu\n", note, tvdb_gpu_index_map_active_count(map), na);
    ++g_failures;
  }

  /* (c) + (a): every batch, all query kinds, interleaved. */
  int ok = 1;
  for (int round = 0; round < 2 && ok; ++round) {
    for (int b = 0; b < NB && ok; ++b) {
      int32_t* ref = (int32_t*)malloc(nqh[b] * sizeof(int32_t));
      int64_t* refi = (int64_t*)malloc(nqh[b] * sizeof(int64_t));
      int32_t* got = (int32_t*)malloc(nqh[b] * sizeof(int32_t));
      int64_t* peri = (int64_t*)malloc(nqh[b] * sizeof(int64_t));
      float* pts = (float*)malloc(nqh[b] * 3 * sizeof(float));
      const float vs[3] = { 0.5f, 0.5f, 0.5f }, og[3] = { -3.25f, 7.5f, -1.75f };

      /* 1. ijk_to_index: reusable vs per-call vs CPU */
      if (!tvdb_ijk_to_index(active, na, q[b], nqh[b], refi)) { ++g_failures; }
      if (tvdb_gpu_ijk_to_index(ctx, active, na, q[b], nqh[b], peri, &e) != TVDB_OK) {
        printf("  FAIL %-22s per-call ijk: %s\n", note, e.message); ok = 0;
      } else if (tvdb_gpu_ijk_to_index_mapped(ctx, map, q[b], nqh[b], got, &e) != TVDB_OK) {
        printf("  FAIL %-22s mapped ijk: %s\n", note, e.message); ok = 0;
      } else {
        size_t bad = 0;
        for (size_t i = 0; i < nqh[b]; ++i)
          if (refi[i] != (int64_t)got[i] || peri[i] != (int64_t)got[i]) ++bad;
        if (bad) { printf("  FAIL %-22s ijk round %d batch %d: %zu/%zu differ\n", note, round, b, bad, nqh[b]); ok = 0; }
        (void)ref;
      }

      /* 2. points_in_grid */
      if (ok) {
        for (size_t i = 0; i < nqh[b]; ++i) {
          pts[3*i+0] = og[0] + ((float)q[b][3*i+0] + 0.5f) * vs[0];
          pts[3*i+1] = og[1] + ((float)q[b][3*i+1] + 0.5f) * vs[1];
          pts[3*i+2] = og[2] + ((float)q[b][3*i+2] + 0.5f) * vs[2];
        }
        if (tvdb_gpu_points_in_grid_mapped(ctx, map, pts, nqh[b], vs, og, got, &e) != TVDB_OK) {
          printf("  FAIL %-22s mapped points: %s\n", note, e.message); ok = 0;
        } else {
          size_t bad = 0;
          for (size_t i = 0; i < nqh[b]; ++i)
            if ((got[i] >= 0) != (refi[i] >= 0)) ++bad;
          if (bad) { printf("  FAIL %-22s points round %d batch %d: %zu differ\n", note, round, b, bad); ok = 0; }
        }
      }

      /* 3. neighbor_counts, both connectivities, against the CPU */
      for (int conn = 6; conn <= 26 && ok; conn += 20) {
        if (!tvdb_neighbor_counts(active, na, conn, ncpu)) { ++g_failures; ok = 0; break; }
        if (tvdb_gpu_neighbor_counts_mapped(ctx, map, conn, ngpu, &e) != TVDB_OK) {
          printf("  FAIL %-22s mapped nbr(%d): %s\n", note, conn, e.message); ok = 0; break;
        }
        size_t bad = 0;
        for (size_t i = 0; i < na; ++i) if (ncpu[i] != ngpu[i]) ++bad;
        if (bad) { printf("  FAIL %-22s nbr(%d) round %d: %zu/%zu differ\n", note, conn, round, bad, na); ok = 0; }
      }
      free(ref); free(refi); free(got); free(peri); free(pts);
    }
  }
  /* A map from a different context must be rejected rather than silently used. */
  if (!ok) ++g_failures;
  else printf("  ok   %-22s na=%zu, %d batches x 2 rounds, all query kinds agree\n",
              note, na, NB);
  tvdb_gpu_index_map_destroy(ctx, map);
  (void)ok;
done:
  for (int b = 0; b < NB; ++b) free(q[b]);
  free(active); free(ncpu); free(ngpu);
}

int main(int argc, char** argv) {
  int want_cuda = (argc > 1 && argv[1][0] == 'c');
  tvdb_error_t e; memset(&e, 0, sizeof e);
  tvdb_gpu_context_t* ctx = NULL;
  tvdb_status_t st = tvdb_gpu_context_create(want_cuda ? TVDB_GPU_BACKEND_CUDA
                                                      : TVDB_GPU_BACKEND_VULKAN,
                                             0, &ctx, &e);
  if (st != TVDB_OK) { printf("no context: %s\n", e.message); return 77; }
  setvbuf(stdout, NULL, _IONBF, 0);
  printf("backend=%s\n", want_cuda ? "cuda" : "vulkan");
  if (!want_cuda && !tvdb_gpu_spirv_available()) {
    printf("SKIP: built without GPU SPIR-V\n");
    tvdb_gpu_context_destroy(ctx); return 77;
  }

  /* TVDB_INDEX_MAP_MIN_ACTIVE is 2048. L=20 yields ~3.1k active voxels, so it
   * is just over the gate, and L=32 is well over. run_case asserts the active
   * set actually clears the gate: without that, raising the gate would silently
   * turn this test back into a linear-scan test and stop covering the map. */
  run_case(ctx, 20, "map-just-over-gate");
  run_case(ctx, 32, "map-large");
  run_sparse_conv(ctx);
  run_reusable(ctx, 20, "reusable-map");
  run_reusable(ctx, 32, "reusable-map-large");

  EXPECT(g_failures == 0);
  tvdb_gpu_context_destroy(ctx);
  printf("index map parity: %s\n", g_failures ? "FAIL" : "OK");
  return g_failures ? 1 : 0;
}
