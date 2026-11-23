/* Sphere/mesh contacts with greedy manifold reduction.
 * SPDX-License-Identifier: Apache-2.0 */
#include "tinyvdb_contact.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void contact_set_error(tvdb_error_t *err, tvdb_status_t status,
                              const char *msg) {
  if (!err) return;
  err->status = status;
  snprintf(err->message, sizeof(err->message), "%s", msg);
  err->byte_offset = 0;
  err->grid_index = -1;
}

void tvdb_contact_set_free(tvdb_contact_set_t *s) {
  if (!s) return;
  free(s->contacts);
  memset(s, 0, sizeof(*s));
}

typedef struct { double v[3]; } vec3;

static vec3 sub3(vec3 a, vec3 b) {
  vec3 r;
  for (int i = 0; i < 3; ++i) r.v[i] = a.v[i] - b.v[i];
  return r;
}
static double dot3(vec3 a, vec3 b) {
  return a.v[0] * b.v[0] + a.v[1] * b.v[1] + a.v[2] * b.v[2];
}
static vec3 addmul3(vec3 a, vec3 b, double s) {
  vec3 r;
  for (int i = 0; i < 3; ++i) r.v[i] = a.v[i] + b.v[i] * s;
  return r;
}
static vec3 scale3(vec3 a, double s) {
  vec3 r;
  for (int i = 0; i < 3; ++i) r.v[i] = a.v[i] * s;
  return r;
}

/* Ericson's closest-point-on-triangle algorithm. */
static vec3 closest_triangle(vec3 p, vec3 a, vec3 b, vec3 c) {
  vec3 ab = sub3(b, a), ac = sub3(c, a), ap = sub3(p, a);
  double d1 = dot3(ab, ap), d2 = dot3(ac, ap);
  if (d1 <= 0.0 && d2 <= 0.0) return a;
  vec3 bp = sub3(p, b);
  double d3 = dot3(ab, bp), d4 = dot3(ac, bp);
  if (d3 >= 0.0 && d4 <= d3) return b;
  double vc = d1 * d4 - d3 * d2;
  if (vc <= 0.0 && d1 >= 0.0 && d3 <= 0.0) return addmul3(a, ab, d1 / (d1 - d3));
  vec3 cp = sub3(p, c);
  double d5 = dot3(ab, cp), d6 = dot3(ac, cp);
  if (d6 >= 0.0 && d5 <= d6) return c;
  double vb = d5 * d2 - d1 * d6;
  if (vb <= 0.0 && d2 >= 0.0 && d6 <= 0.0) return addmul3(a, ac, d2 / (d2 - d6));
  double va = d3 * d6 - d5 * d4;
  if (va <= 0.0 && (d4 - d3) >= 0.0 && (d5 - d6) >= 0.0)
    return addmul3(b, sub3(c, b), (d4 - d3) / ((d4 - d3) + (d5 - d6)));
  double denom = 1.0 / (va + vb + vc);
  return addmul3(addmul3(a, ab, vb * denom), ac, vc * denom);
}

static int cmp_contact(const void *pa, const void *pb) {
  const tvdb_contact_t *a = (const tvdb_contact_t *)pa;
  const tvdb_contact_t *b = (const tvdb_contact_t *)pb;
  if (a->depth > b->depth) return -1;
  if (a->depth < b->depth) return 1;
  return (a->face > b->face) - (a->face < b->face);
}

tvdb_status_t tvdb_mesh_sphere_contacts_ex(const tvdb_triangle_mesh *mesh,
    const double center[3], double radius, double merge_dist,
    tvdb_contact_set_t *out, tvdb_arena_allocator_t *arena, tvdb_error_t *err) {
  if (!mesh || !out || !center || (mesh->face_count && !mesh->faces) ||
      (mesh->vertex_count && !mesh->vertices) || !isfinite(radius) ||
      !isfinite(merge_dist) || radius < 0.0 || merge_dist < 0.0) {
    contact_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "contacts: invalid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t nf = mesh->face_count;
  for (size_t f = 0; f < nf; ++f) {
    uint32_t a = mesh->faces[f].v0, b = mesh->faces[f].v1, c = mesh->faces[f].v2;
    if (a >= mesh->vertex_count || b >= mesh->vertex_count || c >= mesh->vertex_count) {
      contact_set_error(err, TVDB_ERROR_INVALID_DATA, "contacts: bad face index");
      return TVDB_ERROR_INVALID_DATA;
    }
  }
  size_t mark = arena ? arena->current_offset : 0;
  tvdb_contact_t *raw = (tvdb_contact_t *)malloc((nf ? nf : 1) * sizeof(tvdb_contact_t));
  if (!raw) {
    contact_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "contacts: out of memory");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  vec3 p = {{center[0], center[1], center[2]}};
  size_t n = 0;
  for (size_t f = 0; f < nf; ++f) {
    vec3 a = {{mesh->vertices[mesh->faces[f].v0].x, mesh->vertices[mesh->faces[f].v0].y,
               mesh->vertices[mesh->faces[f].v0].z}};
    vec3 b = {{mesh->vertices[mesh->faces[f].v1].x, mesh->vertices[mesh->faces[f].v1].y,
               mesh->vertices[mesh->faces[f].v1].z}};
    vec3 c = {{mesh->vertices[mesh->faces[f].v2].x, mesh->vertices[mesh->faces[f].v2].y,
               mesh->vertices[mesh->faces[f].v2].z}};
    vec3 q = closest_triangle(p, a, b, c);
    vec3 d = sub3(p, q);
    double dist = sqrt(dot3(d, d));
    if (!(dist < radius)) continue;
    tvdb_contact_t ct;
    memset(&ct, 0, sizeof(ct));
    for (int i = 0; i < 3; ++i) ct.point[i] = q.v[i];
    if (dist > 1e-12)
      for (int i = 0; i < 3; ++i) ct.normal[i] = d.v[i] / dist;
    ct.depth = radius - dist;
    ct.face = (uint32_t)f;
    raw[n++] = ct;
  }
  qsort(raw, n, sizeof(tvdb_contact_t), cmp_contact);

  tvdb_contact_t *kept = (tvdb_contact_t *)(arena ?
      tvdb_arena_alloc(arena, (n ? n : 1) * sizeof(tvdb_contact_t)) :
      malloc((n ? n : 1) * sizeof(tvdb_contact_t)));
  if (!kept) {
    free(raw);
    if (arena) arena->current_offset = mark;
    contact_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "contacts: out of memory");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  size_t nk = 0;
  for (size_t i = 0; i < n; ++i) {
    bool far = true;
    for (size_t j = 0; j < nk; ++j) {
      double s = 0.0;
      for (int d = 0; d < 3; ++d) {
        double diff = raw[i].point[d] - kept[j].point[d];
        s += diff * diff;
      }
      if (sqrt(s) <= merge_dist) { far = false; break; }
    }
    if (far) kept[nk++] = raw[i];
  }
  out->contacts = kept;
  out->count = nk;
  free(raw);
  return TVDB_OK;
}

tvdb_status_t tvdb_mesh_aabb(const tvdb_triangle_mesh *mesh,
                             tvdb_aabb_t *out, tvdb_error_t *err) {
  if (!mesh || !out || (mesh->vertex_count && !mesh->vertices)) {
    contact_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "mesh_aabb: invalid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (mesh->vertex_count == 0) {
    for (int d = 0; d < 3; ++d) { out->bmin[d] = 0.0; out->bmax[d] = 0.0; }
    return TVDB_OK;
  }
  for (int d = 0; d < 3; ++d) {
    out->bmin[d] = (double)mesh->vertices[0].x;
    out->bmax[d] = (double)mesh->vertices[0].x;
  }
  for (size_t i = 1; i < mesh->vertex_count; ++i) {
    double v[3] = {(double)mesh->vertices[i].x, (double)mesh->vertices[i].y,
                   (double)mesh->vertices[i].z};
    for (int d = 0; d < 3; ++d) {
      if (v[d] < out->bmin[d]) out->bmin[d] = v[d];
      if (v[d] > out->bmax[d]) out->bmax[d] = v[d];
    }
  }
  return TVDB_OK;
}

tvdb_status_t tvdb_collision_sphere_mesh_ex(const tvdb_triangle_mesh *mesh,
    const double center[3], double radius, double merge_dist,
    tvdb_contact_set_t *out, tvdb_arena_allocator_t *arena, tvdb_error_t *err) {
  if (!out) {
    contact_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "collision: null output");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  out->contacts = NULL;
  out->count = 0;
  tvdb_aabb_t box;
  tvdb_status_t st = tvdb_mesh_aabb(mesh, &box, err);
  if (st != TVDB_OK) return st;
  for (int d = 0; d < 3; ++d) {
    if (center[d] + radius < box.bmin[d] || center[d] - radius > box.bmax[d]) {
      return TVDB_OK;  /* broadphase rejection */
    }
  }
  return tvdb_mesh_sphere_contacts_ex(mesh, center, radius, merge_dist, out, arena, err);
}

bool tvdb_mesh_sphere_contacts(const tvdb_triangle_mesh *mesh,
    const double center[3], double radius, double merge_dist,
    tvdb_contact_set_t *out, tvdb_arena_allocator_t *arena) {
  return tvdb_mesh_sphere_contacts_ex(mesh, center, radius, merge_dist, out, arena, NULL)
         == TVDB_OK;
}
