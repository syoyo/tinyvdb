/* tvdb_tree_accessor: cached lookups match tvdb_tree_get / tvdb_tree_lookup
 * bit for bit (value, active flag and the returned storage pointer) on
 * coherent scans, random probes, and far-apart alternation that forces cache
 * misses, over leaves, internal tiles (flood-filled interior), root tiles and
 * the background. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sdf_tree_fixture.h"
#include "tinyvdb_io.h"
#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_tree_internal.h"

static int failures;
static size_t checks;
#define CHECK(x)                                              \
  do {                                                        \
    if (!(x)) {                                               \
      if (failures < 20)                                      \
        fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x); \
      ++failures;                                             \
    }                                                         \
  } while (0)

static void probe(tvdb_tree_accessor* acc, const int32_t c[3]) {
  const tvdb_tree_index* p = acc->p;
  int a0 = -1, a1 = -1, a2 = -1, a3 = -1;
  float v0 = tvdb_tree_get(p, c, &a0), v1 = tvdb_tree_accessor_get(acc, c, &a1);
  CHECK(!memcmp(&v0, &v1, sizeof(v0)) && a0 == a1);
  const uint8_t *b0, *b1;
  const tvdb_value_t *x0, *x1;
  tvdb_tree_lookup(p, c, &b0, &x0, &a2);
  tvdb_tree_accessor_lookup(acc, c, &b1, &x1, &a3);
  CHECK(b0 == b1 && x0 == x1 && a2 == a3 && a2 == a0);
  ++checks;
}

static uint64_t rng = 0x9e3779b97f4a7c15u;
static int32_t rnd(int32_t lo, int32_t hi) {
  rng ^= rng << 13;
  rng ^= rng >> 7;
  rng ^= rng << 17;
  return lo + (int32_t)(rng % (uint64_t)((int64_t)hi - lo + 1));
}

static void exercise(const tvdb_grid_t* g, const char* name) {
  tvdb_tree_index p;
  if (tvdb_tree_index_create(g, 1, &p, NULL) != TVDB_OK) {
    fprintf(stderr, "%s: index failed\n", name);
    ++failures;
    return;
  }
  tvdb_tree_accessor acc;
  tvdb_tree_accessor_init(&acc, &p);
  int64_t lo[3], hi[3];
  for (int a = 0; a < 3; ++a) {
    lo[a] = (p.has_bbox ? p.bbox_min[a] : 0) - 3;
    hi[a] = (p.has_bbox ? p.bbox_max[a] : 0) + 3;
  }
  size_t before = checks;
  /* Coherent scan, x fastest (the mesher's pattern), on a stride so large
     grids stay quick; then a dense scan of one slab. */
  int64_t step = 1;
  while ((hi[0] - lo[0]) / step * ((hi[1] - lo[1]) / step) * ((hi[2] - lo[2]) / step) >
         2000000)
    ++step;
  for (int64_t z = lo[2]; z < hi[2]; z += step)
    for (int64_t y = lo[1]; y < hi[1]; y += step)
      for (int64_t x = lo[0]; x < hi[0]; x += step) {
        const int32_t c[3] = {(int32_t)x, (int32_t)y, (int32_t)z};
        probe(&acc, c);
      }
  const int64_t zmid = (lo[2] + hi[2]) / 2;
  const int64_t y1 = lo[1] + 400 < hi[1] ? lo[1] + 400 : hi[1],
                x1 = lo[0] + 400 < hi[0] ? lo[0] + 400 : hi[0];
  for (int64_t y = lo[1]; y < y1; ++y)
    for (int64_t x = lo[0]; x < x1; ++x) {
      const int32_t c[3] = {(int32_t)x, (int32_t)y, (int32_t)zmid};
      probe(&acc, c);
    }
  /* Random probes in and around the tree, and anywhere in int32. */
  for (int i = 0; i < 200000; ++i) {
    int32_t c[3];
    for (int a = 0; a < 3; ++a)
      c[a] = (i % 8 == 7) ? rnd(INT32_MIN, INT32_MAX)
                          : rnd((int32_t)lo[a] - 200, (int32_t)hi[a] + 200);
    probe(&acc, c);
  }
  /* Alternate far-apart points, each followed by a near neighbour. */
  for (int i = 0; i < 50000; ++i) {
    int32_t c[3];
    for (int a = 0; a < 3; ++a) c[a] = rnd((int32_t)lo[a], (int32_t)hi[a]);
    probe(&acc, c);
    c[i % 3] += (i & 1) ? 1 : -1;
    probe(&acc, c);
    const int32_t far[3] = {-c[0], c[1] + 9000, c[2]};
    probe(&acc, far);
  }
  printf("%s: %zu probes\n", name, checks - before);
  tvdb_tree_index_destroy(&p);
}

/* A level-set sphere, flood filled so the interior holds internal tiles. */
static int make_sphere(tvdb_grid_t* out, int radius, float band) {
  tvdb_grid_t tmpl;
  sdf_fixture_template(&tmpl);
  tvdb_sparse_grid sg = {0};
  if (!tvdb_sparse_grid_reserve(&sg, 400000)) return 0;
  for (int x = -radius - 3; x <= radius + 3; ++x)
    for (int y = -radius - 3; y <= radius + 3; ++y)
      for (int z = -radius - 3; z <= radius + 3; ++z) {
        float phi = sqrtf((float)(x * x + y * y + z * z)) - (float)radius;
        if (fabsf(phi) < band) {
          sg.coords[sg.count] = (tvdb_vec3i){x - 7, y + 3, z};
          sg.values[sg.count++] = phi;
        }
      }
  tvdb_grid_t g = {0};
  int ok = tvdb_grid_from_sparse_using_template(&tmpl, &sg, "sphere", band, &g);
  if (ok) ok = tvdb_grid_signed_flood_fill(&g, band, -band, out, NULL) == TVDB_OK;
  tvdb_grid_destroy_owned(&g);
  tvdb_sparse_grid_free(&sg);
  return ok;
}

/* Append root tiles (one active, one inactive) next to the existing tree. */
static int add_root_tiles(tvdb_grid_t* g) {
  tvdb_root_node_t* r = &g->tree.nodes[0].u.root;
  const size_t n = r->num_tiles + 2;
  int32_t* o = realloc(r->tile_origins, n * 3 * sizeof(int32_t));
  if (!o) return 0;
  r->tile_origins = o;
  tvdb_value_t* v = realloc(r->tile_values, n * sizeof(tvdb_value_t));
  if (!v) return 0;
  r->tile_values = v;
  int* act = realloc(r->tile_active, n * sizeof(*act));
  if (!act) return 0;
  r->tile_active = act;
  for (int k = 0; k < 2; ++k) {
    const size_t t = r->num_tiles + (size_t)k;
    o[3 * t + 0] = k ? -4096 : 4096;
    o[3 * t + 1] = 0;
    o[3 * t + 2] = k ? 4096 : 0;
    memset(&v[t], 0, sizeof(v[t]));
    v[t].type = TVDB_VALUE_FLOAT;
    v[t].u.f = k ? 2.5f : -1.25f;
    act[t] = !k;
  }
  r->num_tiles = (uint32_t)n;
  return 1;
}

int main(int argc, char** argv) {
  tvdb_grid_t sphere = {0};
  if (!make_sphere(&sphere, 40, 3.0f)) {
    fprintf(stderr, "sphere fixture failed\n");
    return 1;
  }
  exercise(&sphere, "flood-filled sphere");
  if (!add_root_tiles(&sphere)) {
    fprintf(stderr, "root tile setup failed\n");
    return 1;
  }
  exercise(&sphere, "sphere + root tiles");
  tvdb_grid_destroy_owned(&sphere);

  if (argc > 1) {
    tvdb_file_t file;
    tvdb_error_t err;
    if (tvdb_file_open(&file, argv[1], NULL, &err) != TVDB_OK ||
        tvdb_read_grid(&file, 0, &err) != TVDB_OK) {
      fprintf(stderr, "%s: %s\n", argv[1], err.message);
      return 1;
    }
    exercise(&file.grids[0], argv[1]);
    tvdb_file_close(&file);
  }
  if (failures) {
    fprintf(stderr, "%d of %zu probes FAILED\n", failures, checks);
    return 1;
  }
  printf("tree accessor: %zu probes OK\n", checks);
  return 0;
}
