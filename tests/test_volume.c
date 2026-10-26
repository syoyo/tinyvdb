/* tinyvdb_volume: strided dense extraction against brute-force averages,
 * budget fitting, cell_to_world, inactive-as-background, sampling, grid info,
 * metadata round trips through the writer, and argument errors. (Typed grids
 * against OpenVDB are in test_io_openvdb.) */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sdf_tree_fixture.h"
#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_volume.h"

static int failures;
#define CHECK(x)                                                    \
  do {                                                              \
    if (!(x)) {                                                     \
      fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x);       \
      ++failures;                                                   \
    }                                                               \
  } while (0)

/* A level-set sphere (flood filled: interior tiles), voxel size 0.5. */
static int make_sphere(tvdb_grid_t *out, int radius, float band) {
  tvdb_grid_t tmpl;
  sdf_fixture_template(&tmpl);
  tvdb_sparse_grid sg = {0};
  if (!tvdb_sparse_grid_reserve(&sg, 200000)) return 0;
  for (int x = -radius - 3; x <= radius + 3; ++x)
    for (int y = -radius - 3; y <= radius + 3; ++y)
      for (int z = -radius - 3; z <= radius + 3; ++z) {
        float phi = sqrtf((float)(x * x + y * y + z * z)) - (float)radius;
        if (fabsf(phi) < band) {
          sg.coords[sg.count] = (tvdb_vec3i){x + 5, y - 2, z};
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

static void check_strided(const tvdb_grid_t *g) {
  tvdb_volume_sampler_t *s = NULL;
  CHECK(tvdb_volume_sampler_create(g, &s, NULL) == TVDB_OK);
  tvdb_grid_info_t info;
  CHECK(tvdb_grid_get_info(g, &info, NULL) == TVDB_OK);
  for (int stride = 1; stride <= 5; stride += 2) {
    for (int bg = 0; bg <= 1; ++bg) {
      tvdb_dense_volume_options_t o;
      memset(&o, 0, sizeof(o));
      o.stride = stride;
      o.inactive_as_background = bg;
      tvdb_dense_volume_t d = {0};
      CHECK(tvdb_grid_to_dense_volume(g, &o, &d, NULL) == TVDB_OK);
      CHECK(d.stride == stride && d.components == 1);
      double worst = 0;
      for (int w = 0; w < d.dims[2]; ++w)
        for (int v = 0; v < d.dims[1]; ++v)
          for (int u = 0; u < d.dims[0]; ++u) {
            double sum = 0;
            int n = 0;
            for (int k = 0; k < stride; ++k)
              for (int j = 0; j < stride; ++j)
                for (int i = 0; i < stride; ++i) {
                  const int32_t c[3] = {d.index_min[0] + u * stride + i, d.index_min[1] + v * stride + j,
                                        d.index_min[2] + w * stride + k};
                  if (c[0] > info.index_max[0] || c[1] > info.index_max[1] || c[2] > info.index_max[2])
                    continue;
                  float val;
                  int on;
                  tvdb_volume_sampler_get(s, c, &val, &on);
                  sum += bg && !on ? info.background[0] : val;
                  ++n;
                }
            const float got = d.data[u + d.dims[0] * (v + d.dims[1] * w)];
            worst = fmax(worst, fabs(got - sum / n));
          }
      printf("stride %d (inactive %s): %dx%dx%d, max |cell - brute force| %.3g\n", stride,
             bg ? "as background" : "stored", d.dims[0], d.dims[1], d.dims[2], worst);
      CHECK(worst < 1e-5);
      /* Cell centers: cell_to_world maps cell 0 to the center of its voxels. */
      const double off = 0.5 * (stride - 1);
      const double ix = d.index_min[0] + off, iy = d.index_min[1] + off, iz = d.index_min[2] + off;
      for (int a = 0; a < 3; ++a) {
        const double want = info.index_to_world[a][3] + info.index_to_world[a][0] * ix +
                            info.index_to_world[a][1] * iy + info.index_to_world[a][2] * iz;
        CHECK(fabs(d.cell_to_world[a][3] - want) < 1e-12);
        CHECK(fabs(d.cell_to_world[a][a] - info.index_to_world[a][a] * stride) < 1e-12);
      }
      tvdb_dense_volume_free(&d);
    }
  }
  /* Budget: the smallest stride whose cells fit. */
  tvdb_dense_volume_options_t o;
  memset(&o, 0, sizeof(o));
  o.max_voxels = 1000;
  tvdb_dense_volume_t d = {0};
  CHECK(tvdb_grid_to_dense_volume(g, &o, &d, NULL) == TVDB_OK);
  const long cells = (long)d.dims[0] * d.dims[1] * d.dims[2];
  CHECK(cells <= 1000 && d.stride > 1);
  int prev[3];
  for (int a = 0; a < 3; ++a) {
    const int ext = info.index_max[a] - info.index_min[a] + 1;
    prev[a] = (ext + d.stride - 2) / (d.stride - 1);
  }
  CHECK((long)prev[0] * prev[1] * prev[2] > 1000);
  printf("budget 1000: stride %d, %ld cells\n", d.stride, cells);
  /* A fixed stride over budget is an error, and out is preserved. */
  o.stride = 1;
  CHECK(tvdb_grid_to_dense_volume(g, &o, &d, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
  CHECK(d.data != NULL);
  tvdb_dense_volume_free(&d);
  /* A window past the data reads the background. */
  memset(&o, 0, sizeof(o));
  o.use_window = 1;
  for (int a = 0; a < 3; ++a) {
    o.window_min[a] = 1000;
    o.window_max[a] = 1001;
  }
  CHECK(tvdb_grid_to_dense_volume(g, &o, &d, NULL) == TVDB_OK);
  for (int i = 0; i < 8; ++i) CHECK(d.data[i] == info.background[0]);
  tvdb_dense_volume_free(&d);
  /* World samples at voxel centers equal the voxels (both filters). */
  double worst = 0;
  for (int i = 0; i < 200; ++i) {
    const int32_t c[3] = {info.index_min[0] + i % 13, info.index_min[1] + i % 7, info.index_min[2] + i % 11};
    double p[3];
    for (int a = 0; a < 3; ++a)
      p[a] = info.index_to_world[a][3] + info.index_to_world[a][0] * c[0] +
             info.index_to_world[a][1] * c[1] + info.index_to_world[a][2] * c[2];
    float a1, a2, ref;
    int on;
    tvdb_volume_sampler_get(s, c, &ref, &on);
    CHECK(tvdb_volume_sample_world(s, p, 1, TVDB_VOLUME_FILTER_NEAREST, &a1, NULL) == TVDB_OK);
    CHECK(tvdb_volume_sample_world(s, p, 1, TVDB_VOLUME_FILTER_TRILINEAR, &a2, NULL) == TVDB_OK);
    worst = fmax(worst, fmax(fabs(a1 - ref), fabs(a2 - ref)));
  }
  CHECK(worst < 1e-6);
  const double nan_point[3] = {NAN, 0, 0};
  float nv = 0;
  CHECK(tvdb_volume_sample_world(s, nan_point, 1, TVDB_VOLUME_FILTER_NEAREST, &nv, NULL) == TVDB_OK);
  CHECK(isnan(nv));
  CHECK(tvdb_volume_sample_world(s, nan_point, 1, (tvdb_volume_filter_t)7, &nv, NULL) ==
        TVDB_ERROR_INVALID_ARGUMENT);
  tvdb_volume_sampler_destroy(s);
}

/* Caller buffers and slabs: the same cells and layout as the allocating call,
 * whatever the scratch size; too-small buffers fail. */
static void check_buffer(const tvdb_grid_t *g) {
  for (int stride = 1; stride <= 4; stride += 3) {
    tvdb_dense_volume_options_t o;
    memset(&o, 0, sizeof(o));
    o.stride = stride;
    o.inactive_as_background = 1;
    o.vector_magnitude = 1; /* no-op on a scalar grid */
    tvdb_dense_volume_t ref = {0}, lay, lay2;
    CHECK(tvdb_grid_to_dense_volume(g, &o, &ref, NULL) == TVDB_OK);
    CHECK(tvdb_grid_dense_volume_layout(g, &o, &lay, NULL) == TVDB_OK);
    CHECK(lay.data == NULL && lay.components == 1 && lay.stride == stride);
    const size_t n = (size_t)lay.dims[0] * lay.dims[1] * lay.dims[2];
    CHECK(n == (size_t)ref.dims[0] * ref.dims[1] * ref.dims[2]);
    CHECK(!memcmp(lay.cell_to_world, ref.cell_to_world, sizeof(ref.cell_to_world)));
    CHECK(!memcmp(lay.index_min, ref.index_min, sizeof(ref.index_min)));
    float *buf = (float *)malloc((n + 1) * sizeof(float));
    CHECK(tvdb_grid_to_dense_volume_buffer(g, &o, buf, n - 1, NULL, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_grid_to_dense_volume_buffer(g, &o, NULL, n, NULL, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
    for (size_t scratch = 0; scratch <= 1; ++scratch) {
      o.scratch_bytes = scratch; /* 1: one output layer per pass */
      buf[n] = 12345.0f;
      CHECK(tvdb_grid_to_dense_volume_buffer(g, &o, buf, n + 1, &lay2, NULL) == TVDB_OK);
      CHECK(!memcmp(buf, ref.data, n * sizeof(float)));
      CHECK(buf[n] == 12345.0f); /* past the cells: untouched */
      CHECK(lay2.data == NULL && !memcmp(lay2.dims, ref.dims, sizeof(ref.dims)));
    }
    printf("buffer stride %d: %zu cells, identical across scratch sizes\n", stride, n);
    free(buf);
    tvdb_dense_volume_free(&ref);
  }
}

/* Metadata set on a generated grid survives the writer and a header read. */
static void check_metadata(tvdb_grid_t *g) {
  tvdb_error_t err;
  CHECK(tvdb_grid_set_metadata_string(g, "class", "fog volume", &err) == TVDB_OK);
  CHECK(tvdb_grid_set_metadata_string(g, "class", "level set", &err) == TVDB_OK); /* replace */
  tvdb_value_t v;
  memset(&v, 0, sizeof(v));
  v.type = TVDB_VALUE_VEC3F;
  v.u.vec3f[0] = 1.5f;
  v.u.vec3f[1] = -2.0f;
  v.u.vec3f[2] = 4.0f;
  CHECK(tvdb_grid_set_metadata(g, "lightusd:color", &v, &err) == TVDB_OK);
  v.type = TVDB_VALUE_DOUBLE;
  v.u.d = 0.125;
  CHECK(tvdb_grid_set_metadata(g, "lightusd:scale", &v, &err) == TVDB_OK);
  v.type = TVDB_VALUE_NULL;
  CHECK(tvdb_grid_set_metadata(g, "bad", &v, &err) == TVDB_ERROR_INVALID_ARGUMENT);
  tvdb_file_t f;
  tvdb_file_init_for_write(&f, NULL);
  f.grids = g;
  f.num_grids = 1;
  uint8_t *bytes = NULL;
  size_t size = 0;
  CHECK(tvdb_write_to_memory(&f, TVDB_COMPRESS_ZIP, 0, &bytes, &size, &err) == TVDB_OK);
  tvdb_file_t r;
  CHECK(tvdb_file_open_memory(&r, bytes, size, NULL, &err) == TVDB_OK);
  CHECK(tvdb_read_grid_header(&r, 0, &err) == TVDB_OK);
  tvdb_grid_info_t info;
  CHECK(tvdb_grid_get_info(&r.grids[0], &info, &err) == TVDB_OK);
  CHECK(info.grid_class == TVDB_GRID_CLASS_LEVEL_SET && !info.has_tree);
  const tvdb_meta_entry_t *c = tvdb_grid_find_metadata(&r.grids[0], "lightusd:color");
  CHECK(c && c->value.type == TVDB_VALUE_VEC3F && c->value.u.vec3f[1] == -2.0f);
  const tvdb_meta_entry_t *d = tvdb_grid_find_metadata(&r.grids[0], "lightusd:scale");
  CHECK(d && d->value.type == TVDB_VALUE_DOUBLE && d->value.u.d == 0.125);
  CHECK(tvdb_grid_find_metadata(&r.grids[0], "missing") == NULL);
  /* No tree yet: dense and samplers refuse, info still works. */
  tvdb_dense_volume_t dv = {0};
  tvdb_volume_sampler_t *s = NULL;
  CHECK(tvdb_grid_to_dense_volume(&r.grids[0], NULL, &dv, &err) == TVDB_ERROR_INVALID_ARGUMENT);
  CHECK(tvdb_volume_sampler_create(&r.grids[0], &s, &err) == TVDB_ERROR_INVALID_ARGUMENT);
  CHECK(tvdb_read_grid(&r, 0, &err) == TVDB_OK);
  CHECK(tvdb_grid_get_info(&r.grids[0], &info, &err) == TVDB_OK);
  CHECK(info.has_tree && info.grid_class == TVDB_GRID_CLASS_LEVEL_SET);
  tvdb_file_close(&r);
  free(bytes);
  CHECK(!strcmp(tvdb_grid_class_string(TVDB_GRID_CLASS_FOG_VOLUME), "fog volume"));
  CHECK(tvdb_grid_class_from_string("staggered") == TVDB_GRID_CLASS_STAGGERED);
  CHECK(tvdb_grid_class_from_string("other") == TVDB_GRID_CLASS_UNKNOWN);
}

/* Half-stored floats, including subnormals, round-trip exactly (the scalar
 * half decoder used to halve every subnormal; SIMD builds use F16C). */
static void check_half(void) {
  tvdb_grid_t tmpl;
  sdf_fixture_template(&tmpl);
  tvdb_sparse_grid sg = {0};
  CHECK(tvdb_sparse_grid_reserve(&sg, 4096));
  for (int i = 0; i < 2000; ++i) {
    sg.coords[sg.count] = (tvdb_vec3i){i % 20, (i / 20) % 10, i / 200};
    /* m * 2^-24 (subnormal) and m * 2^-22 / 2^-20 (smallest normals). */
    sg.values[sg.count++] = ldexpf((float)(1 + i % 1023), -24 + 2 * (i % 3));
  }
  tvdb_grid_t g = {0};
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "half", 0, &g));
  g.descriptor.save_float_as_half = 1;
  tvdb_file_t f;
  tvdb_file_init_for_write(&f, NULL);
  f.grids = &g;
  f.num_grids = 1;
  uint8_t *bytes = NULL;
  size_t size = 0;
  tvdb_error_t err;
  CHECK(tvdb_write_to_memory(&f, TVDB_COMPRESS_ZIP, 0, &bytes, &size, &err) == TVDB_OK);
  tvdb_file_t r;
  CHECK(tvdb_file_open_memory(&r, bytes, size, NULL, &err) == TVDB_OK);
  CHECK(tvdb_read_grid(&r, 0, &err) == TVDB_OK);
  tvdb_volume_sampler_t *s = NULL;
  CHECK(tvdb_volume_sampler_create(&r.grids[0], &s, &err) == TVDB_OK);
  int bad = 0;
  for (size_t i = 0; i < sg.count && s; ++i) {
    const int32_t c[3] = {sg.coords[i].x, sg.coords[i].y, sg.coords[i].z};
    float v;
    tvdb_volume_sampler_get(s, c, &v, NULL);
    bad += v != sg.values[i];
  }
  printf("half round trip: %d of %zu values differ\n", bad, sg.count);
  CHECK(bad == 0);
  tvdb_volume_sampler_destroy(s);
  tvdb_file_close(&r);
  free(bytes);
  tvdb_grid_destroy_owned(&g);
  tvdb_sparse_grid_free(&sg);
}

int main(void) {
  check_half();
  tvdb_grid_t g = {0};
  CHECK(make_sphere(&g, 12, 3.0f));
  tvdb_grid_info_t info;
  CHECK(tvdb_grid_get_info(&g, &info, NULL) == TVDB_OK);
  CHECK(info.has_tree && info.has_bounds && info.components == 1);
  CHECK(info.value_type == TVDB_VALUE_FLOAT && info.has_transform);
  printf("sphere: index box [%d %d %d]..[%d %d %d], %llu active\n", info.index_min[0],
         info.index_min[1], info.index_min[2], info.index_max[0], info.index_max[1],
         info.index_max[2], (unsigned long long)info.active_voxels);
  check_strided(&g);
  check_buffer(&g);
  check_metadata(&g);
  tvdb_grid_destroy_owned(&g);
  /* Arguments. */
  tvdb_dense_volume_t d = {0};
  CHECK(tvdb_grid_to_dense_volume(NULL, NULL, &d, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
  CHECK(tvdb_grid_get_info(NULL, &info, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
  if (failures) {
    printf("%d failure(s)\n", failures);
    return 1;
  }
  printf("tinyvdb_volume: OK\n");
  return 0;
}
