/* Deterministic convex part decomposition. SPDX-License-Identifier: Apache-2.0 */
#include "tinyvdb_convex_decomp.h"

#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void decomp_set_error(tvdb_error_t *err, tvdb_status_t status,
                             const char *msg) {
  if (!err) return;
  err->status = status;
  snprintf(err->message, sizeof(err->message), "%s", msg);
  err->byte_offset = 0;
  err->grid_index = -1;
}

void tvdb_convex_decomp_free(tvdb_convex_decomp_t *d) {
  if (!d) return;
  free(d->parts);
  free(d->labels);
  memset(d, 0, sizeof(*d));
}

static uint32_t find_root(uint32_t *parent, uint32_t x) {
  while (parent[x] != x) {
    parent[x] = parent[parent[x]];
    x = parent[x];
  }
  return x;
}

static void unite(uint32_t *parent, uint32_t a, uint32_t b) {
  uint32_t ra = find_root(parent, a), rb = find_root(parent, b);
  if (ra == rb) return;
  /* Deterministic: smaller root wins. */
  if (ra < rb) parent[rb] = ra; else parent[ra] = rb;
}

tvdb_status_t tvdb_mesh_convex_decompose_ex(const tvdb_triangle_mesh *mesh,
                                             tvdb_convex_decomp_t *out,
                                             tvdb_arena_allocator_t *arena,
                                             tvdb_error_t *err) {
  if (!mesh || !out || (mesh->vertex_count && !mesh->vertices) ||
      (mesh->face_count && !mesh->faces)) {
    decomp_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "convex_decomp: invalid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t nv = mesh->vertex_count, nf = mesh->face_count;
  for (size_t f = 0; f < nf; ++f) {
    uint32_t a = mesh->faces[f].v0, b = mesh->faces[f].v1, c = mesh->faces[f].v2;
    if (a >= nv || b >= nv || c >= nv) {
      decomp_set_error(err, TVDB_ERROR_INVALID_DATA, "convex_decomp: bad face index");
      return TVDB_ERROR_INVALID_DATA;
    }
  }
  size_t mark = arena ? arena->current_offset : 0;
  uint32_t *parent = (uint32_t *)malloc((nv ? nv : 1) * sizeof(uint32_t));
  double *lo = (double *)malloc((nv * 3 + 1) * sizeof(double));
  double *hi = (double *)malloc((nv * 3 + 1) * sizeof(double));
  uint32_t *first = (uint32_t *)malloc((nv ? nv : 1) * sizeof(uint32_t));
  uint32_t *face_count = (uint32_t *)calloc(nv ? nv : 1, sizeof(uint32_t));
  uint32_t *order = (uint32_t *)malloc((nv ? nv : 1) * sizeof(uint32_t));
  if (!parent || !lo || !hi || !first || !face_count || !order) {
    free(parent); free(lo); free(hi); free(first); free(face_count); free(order);
    if (arena) arena->current_offset = mark;
    decomp_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "convex_decomp: out of memory");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  for (size_t i = 0; i < nv; ++i) {
    parent[i] = (uint32_t)i;
    first[i] = UINT32_MAX;
  }
  for (size_t f = 0; f < nf; ++f) {
    const tvdb_triangle *t = &mesh->faces[f];
    unite(parent, t->v0, t->v1);
    unite(parent, t->v0, t->v2);
  }
  for (size_t i = 0; i < nv; ++i) {
    uint32_t r = find_root(parent, (uint32_t)i);
    if (first[r] == UINT32_MAX) first[r] = (uint32_t)i;
  }
  for (size_t f = 0; f < nf; ++f) {
    const tvdb_triangle *t = &mesh->faces[f];
    uint32_t r = find_root(parent, t->v0);
    if (first[r] > t->v0) first[r] = t->v0;
    ++face_count[r];
  }
  size_t np = 0;
  for (size_t i = 0; i < nv; ++i)
    if (first[i] != UINT32_MAX) order[np++] = (uint32_t)i;
  /* Components are ordered by their lowest original vertex index. */
  for (size_t i = 1; i < np; ++i) {
    uint32_t k = order[i];
    size_t j = i;
    while (j > 0 && first[order[j - 1]] > first[k]) { order[j] = order[j - 1]; --j; }
    order[j] = k;
  }
  for (size_t p = 0; p < np; ++p) {
    uint32_t r = order[p];
    for (int d = 0; d < 3; ++d) { lo[r * 3 + d] = DBL_MAX; hi[r * 3 + d] = -DBL_MAX; }
  }
  for (size_t i = 0; i < nv; ++i) {
    uint32_t r = find_root(parent, (uint32_t)i);
    if (first[r] == UINT32_MAX) continue;
    const tvdb_vec3f *v = &mesh->vertices[i];
    double q[3] = {v->x, v->y, v->z};
    for (int d = 0; d < 3; ++d) {
      if (q[d] < lo[r * 3 + d]) lo[r * 3 + d] = q[d];
      if (q[d] > hi[r * 3 + d]) hi[r * 3 + d] = q[d];
    }
  }

  tvdb_convex_part_t *parts = (tvdb_convex_part_t *)(arena ?
      tvdb_arena_alloc(arena, (np ? np : 1) * sizeof(tvdb_convex_part_t)) :
      malloc((np ? np : 1) * sizeof(tvdb_convex_part_t)));
  uint32_t *labels = (uint32_t *)(arena ?
      tvdb_arena_alloc(arena, (nv ? nv : 1) * sizeof(uint32_t)) :
      malloc((nv ? nv : 1) * sizeof(uint32_t)));
  if (!parts || !labels) {
    if (!arena) { free(parts); free(labels); }
    free(parent); free(lo); free(hi); free(first); free(face_count); free(order);
    if (arena) arena->current_offset = mark;
    decomp_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "convex_decomp: out of memory");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  for (size_t p = 0; p < np; ++p) {
    uint32_t r = order[p];
    for (int d = 0; d < 3; ++d) { parts[p].lo[d] = lo[r * 3 + d]; parts[p].hi[d] = hi[r * 3 + d]; }
    parts[p].first_face = first[r];
    parts[p].face_count = face_count[r];
  }
  for (size_t i = 0; i < nv; ++i) {
    uint32_t r = find_root(parent, (uint32_t)i);
    labels[i] = 0;
    for (size_t p = 0; p < np; ++p)
      if (order[p] == r) { labels[i] = (uint32_t)p; break; }
  }
  out->parts = parts; out->part_count = np;
  out->labels = labels; out->label_count = nv;

  free(parent); free(lo); free(hi); free(first); free(face_count); free(order);
  return TVDB_OK;
}

tvdb_status_t tvdb_points_convex_hull_ex(const double *points, size_t count,
    const tvdb_convex_hull_options_t *options, tvdb_triangle_mesh *out,
    tvdb_arena_allocator_t *arena, tvdb_error_t *err) {
  if (!points || !out || !options || count < 3 ||
      (out->vertex_capacity && !out->vertices) ||
      (out->face_capacity && !out->faces)) {
    decomp_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "convex_hull: invalid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  double eps = options->eps > 0.0 ? options->eps : 1e-9;
  for (size_t i = 0; i < count; ++i)
    for (int d = 0; d < 3; ++d)
      if (!isfinite(points[3 * i + d])) {
        decomp_set_error(err, TVDB_ERROR_INVALID_DATA, "convex_hull: nonfinite point");
        return TVDB_ERROR_INVALID_DATA;
      }
  size_t mark = arena ? arena->current_offset : 0;
  tvdb_triangle *faces = (tvdb_triangle *)malloc(count * count * sizeof(tvdb_triangle));
  if (!faces) {
    decomp_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "convex_hull: out of memory");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  size_t nf = 0;
  for (size_t i = 0; i < count; ++i)
    for (size_t j = i + 1; j < count; ++j)
      for (size_t k = j + 1; k < count; ++k) {
        double ux = points[3*j] - points[3*i], uy = points[3*j+1] - points[3*i+1],
               uz = points[3*j+2] - points[3*i+2];
        double vx = points[3*k] - points[3*i], vy = points[3*k+1] - points[3*i+1],
               vz = points[3*k+2] - points[3*i+2];
        double nx = uy*vz - uz*vy, ny = uz*vx - ux*vz, nz = ux*vy - uy*vx;
        if (sqrt(nx*nx + ny*ny + nz*nz) <= eps) continue;
        bool support = true;
        for (size_t l = 0; l < count; ++l) {
          if (l == i || l == j || l == k) continue;
          double d = nx * (points[3*l] - points[3*i]) +
                     ny * (points[3*l+1] - points[3*i+1]) +
                     nz * (points[3*l+2] - points[3*i+2]);
          if (d > eps) { support = false; break; }
        }
        if (support) {
          faces[nf].v0 = (uint32_t)i; faces[nf].v1 = (uint32_t)j; faces[nf].v2 = (uint32_t)k;
          ++nf;
        }
      }
  if (nf == 0) {
    free(faces);
    if (arena) arena->current_offset = mark;
    decomp_set_error(err, TVDB_ERROR_INVALID_DATA,
                     "convex_hull: no strict supporting faces (coplanar input?)");
    return TVDB_ERROR_INVALID_DATA;
  }
  tvdb_vec3f *verts = (tvdb_vec3f *)(arena ?
      tvdb_arena_alloc(arena, count * sizeof(tvdb_vec3f)) :
      malloc(count * sizeof(tvdb_vec3f)));
  tvdb_triangle *ofaces = (tvdb_triangle *)(arena ?
      tvdb_arena_alloc(arena, nf * sizeof(tvdb_triangle)) :
      malloc(nf * sizeof(tvdb_triangle)));
  if (!verts || !ofaces) {
    if (!arena) { free(verts); free(ofaces); }
    free(faces);
    if (arena) arena->current_offset = mark;
    decomp_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "convex_hull: out of memory");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  for (size_t i = 0; i < count; ++i) {
    verts[i].x = (float)points[3*i];
    verts[i].y = (float)points[3*i+1];
    verts[i].z = (float)points[3*i+2];
  }
  memcpy(ofaces, faces, nf * sizeof(tvdb_triangle));
  if (!arena) { free(out->vertices); free(out->faces); }
  out->vertices = verts; out->vertex_count = count; out->vertex_capacity = count;
  out->faces = ofaces; out->face_count = nf; out->face_capacity = nf;
  free(faces);
  return TVDB_OK;
}

bool tvdb_points_convex_hull(const double *points, size_t count,
    tvdb_triangle_mesh *out, tvdb_arena_allocator_t *arena) {
  tvdb_convex_hull_options_t opt = {0.0};
  return tvdb_points_convex_hull_ex(points, count, &opt, out, arena, NULL) == TVDB_OK;
}

bool tvdb_mesh_convex_decompose(const tvdb_triangle_mesh *mesh,
                                 tvdb_convex_decomp_t *out,
                                 tvdb_arena_allocator_t *arena) {
  return tvdb_mesh_convex_decompose_ex(mesh, out, arena, NULL) == TVDB_OK;
}
