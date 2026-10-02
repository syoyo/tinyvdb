#include "tinyvdb_jagged.h"
#include "tinyvdb_checked.h"

#include <stdlib.h>
#include <string.h>

/* Check signed container counts before conversion, addition, or allocation. */
static bool tvdb_batch_bytes(int64_t count, size_t width, size_t* bytes) {
  return count >= 0 && (uint64_t)count <= SIZE_MAX &&
         tvdb_size_mul((size_t)count, width, bytes);
}

static bool tvdb_jagged_valid(const tvdb_jagged_t* jt) {
  size_t bytes, width;
  if (!jt || jt->num_lists < 0 || jt->num_lists == INT64_MAX ||
      jt->channels < 1 || !jt->offsets ||
      !tvdb_batch_bytes(jt->num_lists + 1, sizeof(int64_t), &bytes) ||
      jt->offsets[0] != 0 ||
      !tvdb_size_mul((size_t)jt->channels, sizeof(float), &width)) return false;
  for (int64_t i = 0; i < jt->num_lists; ++i)
    if (jt->offsets[i + 1] < jt->offsets[i]) return false;
  return tvdb_batch_bytes(jt->offsets[jt->num_lists],
                           width, &bytes) &&
         (jt->offsets[jt->num_lists] == 0 || jt->data);
}

// ---- JaggedTensor -----------------------------------------------------------

void tvdb_jagged_init(tvdb_jagged_t* jt) {
  if (!jt) return;
  jt->data = NULL; jt->offsets = NULL; jt->num_lists = 0; jt->channels = 0;
}

void tvdb_jagged_free(tvdb_jagged_t* jt) {
  if (!jt) return;
  free(jt->data); free(jt->offsets);
  tvdb_jagged_init(jt);
}

static bool tvdb_jagged_alloc(tvdb_jagged_t* jt, int64_t num_lists,
                              const int64_t* list_sizes, int channels) {
  tvdb_jagged_init(jt);
  size_t bytes, width;
  if (num_lists < 0 || num_lists == INT64_MAX || channels < 1 ||
      (num_lists > 0 && !list_sizes) ||
      !tvdb_batch_bytes(num_lists + 1, sizeof(int64_t), &bytes) ||
      !tvdb_size_mul((size_t)channels, sizeof(float), &width)) return false;
  int64_t* offsets = (int64_t*)malloc(bytes);
  if (!offsets) return false;
  offsets[0] = 0;
  for (int64_t i = 0; i < num_lists; ++i) {
    int64_t s = list_sizes[i];
    if (s < 0 || s > INT64_MAX - offsets[i]) { free(offsets); return false; }
    offsets[i + 1] = offsets[i] + s;
  }
  int64_t total = offsets[num_lists];
  if (!tvdb_batch_bytes(total > 0 ? total : 1, width, &bytes)) { free(offsets); return false; }
  float* data = (float*)calloc(1, bytes);
  if (!data) { free(offsets); return false; }
  jt->data = data; jt->offsets = offsets; jt->num_lists = num_lists; jt->channels = channels;
  return true;
}

bool tvdb_jagged_create(tvdb_jagged_t* jt, int64_t num_lists,
                        const int64_t* list_sizes, int channels) {
  if (!jt) return false;
  return tvdb_jagged_alloc(jt, num_lists, list_sizes, channels);
}

bool tvdb_jagged_from_lists(tvdb_jagged_t* jt, int64_t num_lists,
                            const float* const* list_data,
                            const int64_t* list_sizes, int channels) {
  if (!jt || !tvdb_jagged_alloc(jt, num_lists, list_sizes, channels)) return false;
  for (int64_t i = 0; i < num_lists; ++i) {
    int64_t s = list_sizes[i];
    if (s > 0 && list_data && list_data[i])
      memcpy(jt->data + (size_t)jt->offsets[i] * (size_t)channels, list_data[i],
             (size_t)s * (size_t)channels * sizeof(float));
  }
  return true;
}

int64_t tvdb_jagged_total(const tvdb_jagged_t* jt) {
  return (jt && jt->offsets && jt->num_lists >= 0) ? jt->offsets[jt->num_lists] : 0;
}

int64_t tvdb_jagged_list_count(const tvdb_jagged_t* jt) { return jt ? jt->num_lists : 0; }

int64_t tvdb_jagged_list_size(const tvdb_jagged_t* jt, int64_t i) {
  if (!jt || !jt->offsets || i < 0 || i >= jt->num_lists) return 0;
  return jt->offsets[i + 1] - jt->offsets[i];
}

float* tvdb_jagged_list_ptr(const tvdb_jagged_t* jt, int64_t i, int64_t* out_size) {
  if (!jt || !jt->offsets || i < 0 || i >= jt->num_lists) { if (out_size) *out_size = 0; return NULL; }
  if (out_size) *out_size = jt->offsets[i + 1] - jt->offsets[i];
  return jt->data ? jt->data + (size_t)jt->offsets[i] * (size_t)jt->channels : NULL;
}

bool tvdb_jagged_concat(tvdb_jagged_t* out, const tvdb_jagged_t* const* parts,
                        int64_t num_parts) {
  if (!out || num_parts < 0 || (num_parts > 0 && !parts)) return false;
  for (int64_t k = 0; k < num_parts; ++k)
    if (parts[k] == out) return false;
  tvdb_jagged_init(out);
  int channels = 0;
  int64_t total_lists = 0;
  for (int64_t k = 0; k < num_parts; ++k) {
    if (!tvdb_jagged_valid(parts[k]) ||
        parts[k]->num_lists > INT64_MAX - total_lists) return false;
    if (k == 0) channels = parts[k]->channels;
    else if (parts[k]->channels != channels) return false;
    total_lists += parts[k]->num_lists;
  }
  if (channels < 1) channels = 1;
  size_t bytes;
  if (!tvdb_batch_bytes(total_lists > 0 ? total_lists : 1, sizeof(int64_t), &bytes)) return false;
  int64_t* sizes = (int64_t*)malloc(bytes);
  if (!sizes) return false;
  int64_t li = 0;
  for (int64_t k = 0; k < num_parts; ++k)
    for (int64_t j = 0; j < parts[k]->num_lists; ++j)
      sizes[li++] = tvdb_jagged_list_size(parts[k], j);
  if (!tvdb_jagged_alloc(out, total_lists, sizes, channels)) { free(sizes); return false; }
  free(sizes);
  li = 0;
  for (int64_t k = 0; k < num_parts; ++k) {
    for (int64_t j = 0; j < parts[k]->num_lists; ++j) {
      int64_t s = tvdb_jagged_list_size(parts[k], j);
      if (s > 0) {
        const float* src = parts[k]->data + (size_t)parts[k]->offsets[j] * (size_t)channels;
        memcpy(out->data + (size_t)out->offsets[li] * (size_t)channels, src,
               (size_t)s * (size_t)channels * sizeof(float));
      }
      ++li;
    }
  }
  return true;
}

typedef enum { TVDB_RED_SUM, TVDB_RED_MEAN, TVDB_RED_MAX, TVDB_RED_MIN } tvdb_reduce_op;

static bool tvdb_jagged_reduce(const tvdb_jagged_t* jt, float* out, tvdb_reduce_op op) {
  size_t bytes, width;
  if (!out || !tvdb_jagged_valid(jt) ||
      !tvdb_size_mul((size_t)jt->channels, sizeof(float), &width) ||
      !tvdb_batch_bytes(jt->num_lists, width, &bytes)) return false;
  const int c = jt->channels;

  /* Channel is the inner loop, not the outer one. The original read
     base[e*c + ch] with ch outside, so every step advanced c floats and touched a
     new cache line; with ch inside, a row is read once, contiguously, and the
     per-channel accumulation vectorizes. Each channel still visits e in ascending
     order, so the sums stay bit-identical to the previous loop -- this is a
     reordering of the loops, not of the arithmetic. */
  #define TVDB_JAGGED_ACC(I, STACKBUF)                                                      \
    do {                                                                                     \
      const int64_t i_ = (I);                                                                 \
      const int64_t s_ = jt->offsets[i_ + 1] - jt->offsets[i_];                               \
      const float* base_ = jt->data ? jt->data + (size_t)jt->offsets[i_] * (size_t)c : NULL;   \
      float* acc_ = (STACKBUF);                                                                \
      for (int ch = 0; ch < c; ++ch) acc_[ch] = 0.0f;                                          \
      if (s_ > 0 && base_) {                                                                   \
        for (int ch = 0; ch < c; ++ch) acc_[ch] = base_[ch];                                    \
        for (int64_t e = 1; e < s_; ++e) {                                                      \
          const float* row_ = base_ + (size_t)e * (size_t)c;                                      \
          for (int ch = 0; ch < c; ++ch) {                                                        \
            const float v_ = row_[ch];                                                            \
            switch (op) {                                                                        \
              case TVDB_RED_SUM: case TVDB_RED_MEAN: acc_[ch] += v_; break;                       \
              case TVDB_RED_MAX: if (v_ > acc_[ch]) acc_[ch] = v_; break;                          \
              case TVDB_RED_MIN: if (v_ < acc_[ch]) acc_[ch] = v_; break;                          \
            }                                                                                     \
          }                                                                                        \
        }                                                                                          \
        if (op == TVDB_RED_MEAN)                                                                  \
          for (int ch = 0; ch < c; ++ch) acc_[ch] /= (float)s_;                                  \
      }                                                                                            \
      for (int ch = 0; ch < c; ++ch)                                                              \
        out[(size_t)i_ * (size_t)c + ch] = acc_[ch];                                                \
    } while (0)

  /* Each list writes only its own c outputs and reads a read-only view, so the
     outer loop parallelizes once the accumulator is per-thread rather than
     shared. Channel counts are small in practice, so the accumulator lives on the
     stack; a wider one falls back to a serial heap buffer. */
  enum { TVDB_JAGGED_STACK_CHANNELS = 64 };
  if (c <= TVDB_JAGGED_STACK_CHANNELS) {
    #pragma omp parallel for schedule(static)
    for (long long ii = 0; ii < (long long)jt->num_lists; ++ii) {
      float accbuf[TVDB_JAGGED_STACK_CHANNELS];
      TVDB_JAGGED_ACC((int64_t)ii, accbuf);
    }
  } else {
    float* accheap = (float*)malloc((size_t)c * sizeof(float));
    if (!accheap) return false;
    for (int64_t i = 0; i < jt->num_lists; ++i) TVDB_JAGGED_ACC(i, accheap);
    free(accheap);
  }
  #undef TVDB_JAGGED_ACC
  return true;
}

bool tvdb_jagged_sum(const tvdb_jagged_t* jt, float* out)  { return tvdb_jagged_reduce(jt, out, TVDB_RED_SUM); }
bool tvdb_jagged_mean(const tvdb_jagged_t* jt, float* out) { return tvdb_jagged_reduce(jt, out, TVDB_RED_MEAN); }
bool tvdb_jagged_max(const tvdb_jagged_t* jt, float* out)  { return tvdb_jagged_reduce(jt, out, TVDB_RED_MAX); }
bool tvdb_jagged_min(const tvdb_jagged_t* jt, float* out)  { return tvdb_jagged_reduce(jt, out, TVDB_RED_MIN); }

// ---- GridBatch --------------------------------------------------------------

void tvdb_grid_batch_init(tvdb_grid_batch_t* gb) {
  if (!gb) return;
  gb->coords = NULL; gb->values = NULL; gb->offsets = NULL; gb->num_grids = 0;
  gb->voxel_size = NULL; gb->origin = NULL;
}

void tvdb_grid_batch_free(tvdb_grid_batch_t* gb) {
  if (!gb) return;
  free(gb->coords); free(gb->values); free(gb->offsets);
  free(gb->voxel_size); free(gb->origin);
  tvdb_grid_batch_init(gb);
}

bool tvdb_grid_batch_from_grids(tvdb_grid_batch_t* gb, const tvdb_sparse_grid* grids, int64_t n) {
  if (!gb) return false;
  tvdb_grid_batch_init(gb);
  size_t offset_bytes, vs_bytes, org_bytes;
  if (n < 0 || n == INT64_MAX || (n > 0 && !grids) ||
      !tvdb_batch_bytes(n + 1, sizeof(int64_t), &offset_bytes) ||
      !tvdb_batch_bytes(n > 0 ? n : 1, sizeof(float), &vs_bytes) ||
      !tvdb_batch_bytes(n > 0 ? n : 1, 3 * sizeof(float), &org_bytes)) return false;
  int64_t* offsets = (int64_t*)malloc(offset_bytes);
  float* vs = (float*)malloc(vs_bytes);
  float* org = (float*)malloc(org_bytes);
  if (!offsets || !vs || !org) { free(offsets); free(vs); free(org); return false; }
  offsets[0] = 0;
  for (int64_t i = 0; i < n; ++i) {
    if (grids[i].count > (uint64_t)(INT64_MAX - offsets[i]) ||
        (grids[i].count && (!grids[i].coords || !grids[i].values))) {
      free(offsets); free(vs); free(org); return false;
    }
    offsets[i + 1] = offsets[i] + (int64_t)grids[i].count;
    vs[i] = grids[i].voxel_size;
    org[3*(size_t)i+0] = grids[i].ox; org[3*(size_t)i+1] = grids[i].oy; org[3*(size_t)i+2] = grids[i].oz;
  }
  int64_t total = offsets[n];
  size_t coord_bytes, value_bytes;
  if (!tvdb_batch_bytes(total > 0 ? total : 1, sizeof(tvdb_vec3i), &coord_bytes) ||
      !tvdb_batch_bytes(total > 0 ? total : 1, sizeof(float), &value_bytes)) {
    free(offsets); free(vs); free(org); return false;
  }
  tvdb_vec3i* coords = (tvdb_vec3i*)malloc(coord_bytes);
  float* values = (float*)malloc(value_bytes);
  if (!coords || !values) { free(offsets); free(vs); free(org); free(coords); free(values); return false; }
  for (int64_t i = 0; i < n; ++i) {
    size_t cnt = grids[i].count;
    if (cnt > 0) {
      memcpy(coords + offsets[i], grids[i].coords, cnt * sizeof(tvdb_vec3i));
      memcpy(values + offsets[i], grids[i].values, cnt * sizeof(float));
    }
  }
  gb->coords = coords; gb->values = values; gb->offsets = offsets;
  gb->num_grids = n; gb->voxel_size = vs; gb->origin = org;
  return true;
}

int64_t tvdb_grid_batch_size(const tvdb_grid_batch_t* gb) { return gb ? gb->num_grids : 0; }

int64_t tvdb_grid_batch_total_voxels(const tvdb_grid_batch_t* gb) {
  return (gb && gb->offsets && gb->num_grids >= 0) ? gb->offsets[gb->num_grids] : 0;
}

int64_t tvdb_grid_batch_grid_size(const tvdb_grid_batch_t* gb, int64_t i) {
  if (!gb || !gb->offsets || i < 0 || i >= gb->num_grids) return 0;
  return gb->offsets[i + 1] - gb->offsets[i];
}

bool tvdb_grid_batch_view(const tvdb_grid_batch_t* gb, int64_t i, tvdb_sparse_grid* out_view) {
  if (!gb || !gb->offsets || !out_view || i < 0 || i >= gb->num_grids) return false;
  out_view->coords = gb->coords + gb->offsets[i];
  out_view->values = gb->values + gb->offsets[i];
  out_view->count = (size_t)(gb->offsets[i + 1] - gb->offsets[i]);
  out_view->capacity = 0;  // view: not owned, must not be freed/grown
  out_view->voxel_size = gb->voxel_size[i];
  out_view->ox = gb->origin[3*i+0]; out_view->oy = gb->origin[3*i+1]; out_view->oz = gb->origin[3*i+2];
  return true;
}

bool tvdb_grid_batch_views(const tvdb_grid_batch_t* gb, tvdb_sparse_grid* out_views) {
  if (!gb || !out_views) return false;
  for (int64_t i = 0; i < gb->num_grids; ++i)
    if (!tvdb_grid_batch_view(gb, i, &out_views[i])) return false;
  return true;
}

bool tvdb_grid_batch_values_jagged(const tvdb_grid_batch_t* gb, tvdb_jagged_t* out) {
  if (!gb || !gb->offsets || !out || gb->num_grids < 0 ||
      gb->num_grids == INT64_MAX) return false;
  size_t checked_bytes;
  if (!tvdb_batch_bytes(gb->num_grids + 1, sizeof(int64_t), &checked_bytes) ||
      gb->offsets[0] != 0) return false;
  for (int64_t i = 0; i < gb->num_grids; ++i)
    if (gb->offsets[i + 1] < gb->offsets[i]) return false;
  if (!tvdb_batch_bytes(gb->offsets[gb->num_grids], sizeof(float), &checked_bytes) ||
      (gb->offsets[gb->num_grids] && !gb->values)) return false;
  int64_t n = gb->num_grids;
  size_t bytes;
  if (!tvdb_batch_bytes(n > 0 ? n : 1, sizeof(int64_t), &bytes) || n < 0) return false;
  int64_t* sizes = (int64_t*)malloc(bytes);
  if (!sizes) return false;
  for (int64_t i = 0; i < n; ++i) sizes[i] = gb->offsets[i + 1] - gb->offsets[i];
  bool ok = tvdb_jagged_create(out, n, sizes, 1);
  free(sizes);
  if (!ok) return false;
  int64_t total = gb->offsets[n];
  if (total > 0) memcpy(out->data, gb->values, (size_t)total * sizeof(float));
  return true;
}

int64_t tvdb_grid_batch_ijk_to_index(const tvdb_grid_batch_t* gb, int64_t b, const int32_t ijk[3]) {
  if (!gb || !gb->offsets || !ijk || b < 0 || b >= gb->num_grids) return -1;
  int64_t start = gb->offsets[b], end = gb->offsets[b + 1];
  for (int64_t i = start; i < end; ++i)
    if (gb->coords[i].x == ijk[0] && gb->coords[i].y == ijk[1] && gb->coords[i].z == ijk[2])
      return i - start;  // local index within grid b
  return -1;
}
