/* Deterministic QEM-ranked edge-collapse simplification. See the header for
 * the contract. SPDX-License-Identifier: Apache-2.0 */
#include "tinyvdb_mesh_simplify.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void simplify_set_error(tvdb_error_t *err, tvdb_status_t status,
                               const char *msg) {
  if (!err) return;
  err->status = status;
  snprintf(err->message, sizeof(err->message), "%s", msg);
  err->byte_offset = 0;
  err->grid_index = -1;
}

/* ---- quadric algebra (mirrors Vdb/Qem.lean) ------------------------------ */

typedef struct {
  double a[6]; /* a00 a01 a02 a11 a12 a22 */
  double b[3];
  double c;
} quadric_t;

static void quadric_zero(quadric_t *q) {
  memset(q, 0, sizeof(*q));
}

static void quadric_add(quadric_t *q, const quadric_t *r) {
  for (int i = 0; i < 6; ++i) q->a[i] += r->a[i];
  for (int i = 0; i < 3; ++i) q->b[i] += r->b[i];
  q->c += r->c;
}

static double quadric_eval(const quadric_t *q, const double v[3]) {
  return q->a[0] * v[0] * v[0] + 2.0 * q->a[1] * v[0] * v[1] +
         2.0 * q->a[2] * v[0] * v[2] + q->a[3] * v[1] * v[1] +
         2.0 * q->a[4] * v[1] * v[2] + q->a[5] * v[2] * v[2] +
         2.0 * (q->b[0] * v[0] + q->b[1] * v[1] + q->b[2] * v[2]) + q->c;
}

static void quadric_plane(quadric_t *q, const double n[3], double d) {
  q->a[0] = n[0] * n[0];
  q->a[1] = n[0] * n[1];
  q->a[2] = n[0] * n[2];
  q->a[3] = n[1] * n[1];
  q->a[4] = n[1] * n[2];
  q->a[5] = n[2] * n[2];
  for (int i = 0; i < 3; ++i) q->b[i] = -d * n[i];
  q->c = d * d;
}

/* ---- edge helpers -------------------------------------------------------- */

static uint64_t edge_key(uint32_t a, uint32_t b) {
  if (a > b) { uint32_t t = a; a = b; b = t; }
  return ((uint64_t)a << 32) | b;
}

static int cmp_u64(const void *pa, const void *pb) {
  uint64_t a = *(const uint64_t *)pa, b = *(const uint64_t *)pb;
  return (a > b) - (a < b);
}

typedef struct {
  double cost;
  uint32_t i, j;
} candidate_t;

static int cmp_candidate(const void *pa, const void *pb) {
  const candidate_t *a = (const candidate_t *)pa;
  const candidate_t *b = (const candidate_t *)pb;
  /* Snap near-equal costs: mathematically equal rational costs can arrive at
     slightly different doubles through different accumulation orders. The
     exact-rational Lean twin ties on the same (i,j) pair. */
  double diff = a->cost - b->cost;
  if (fabs(diff) > 1e-9) return diff < 0 ? -1 : 1;
  if (a->i != b->i) return a->i < b->i ? -1 : 1;
  return (a->j > b->j) - (a->j < b->j);
}

static bool face_has(const uint32_t f[3], uint32_t v) {
  return f[0] == v || f[1] == v || f[2] == v;
}

static bool face_degenerate(const uint32_t f[3]) {
  return f[0] == f[1] || f[1] == f[2] || f[0] == f[2];
}

static bool face_equal(const uint32_t a[3], const uint32_t b[3]) {
  return a[0] == b[0] && a[1] == b[1] && a[2] == b[2];
}

/* The two endpoints of an edge must share exactly two other vertices: the
 * opposite corners of the two incident faces (the link condition). */
static bool link_ok(const uint32_t *faces, size_t nfaces, const bool *dead,
                    uint32_t a, uint32_t b) {
  uint32_t opp[2];
  int n = 0;
  for (size_t f = 0; f < nfaces; ++f) {
    if (dead[f] || !face_has(faces + 3 * f, a) || !face_has(faces + 3 * f, b))
      continue;
    uint32_t k = faces[3 * f] == a || faces[3 * f] == b ? 0 : faces[3 * f];
    if (faces[3 * f + 1] != a && faces[3 * f + 1] != b) k = faces[3 * f + 1];
    if (faces[3 * f + 2] != a && faces[3 * f + 2] != b) k = faces[3 * f + 2];
    if (n == 0 || opp[0] != k) {
      if (n >= 2) return false;
      opp[n++] = k;
    }
  }
  return n == 2;
}

/* Directed-edge closure, no loops and no repeated directed edges. */
static bool closed_mesh(const uint32_t *faces, size_t nfaces, const bool *dead) {
  uint64_t *keys = (uint64_t *)malloc(3 * nfaces * sizeof(uint64_t));
  if (!keys) return false;
  size_t n = 0;
  for (size_t f = 0; f < nfaces; ++f) {
    if (dead[f]) continue;
    const uint32_t *t = faces + 3 * f;
    if (face_degenerate(t)) { free(keys); return false; }
    for (int e = 0; e < 3; ++e) {
      uint32_t u = t[e], v = t[(e + 1) % 3];
      if (u == v) { free(keys); return false; }
      keys[n++] = ((uint64_t)u << 32) | v;
    }
  }
  qsort(keys, n, sizeof(uint64_t), cmp_u64);
  for (size_t k = 1; k < n; ++k)
    if (keys[k] == keys[k - 1]) { free(keys); return false; }
  bool ok = true;
  for (size_t k = 0; k < n; ++k) {
    uint64_t e = keys[k];
    uint64_t rev = ((e & 0xffffffffu) << 32) | (e >> 32);
    if (!bsearch(&rev, keys, n, sizeof(uint64_t), cmp_u64)) { ok = false; break; }
  }
  free(keys);
  return ok;
}

static bool ranges_overlap(const void *a, size_t abytes,
                           const void *b, size_t bbytes) {
  if (!abytes || !bbytes || !a || !b) return false;
  uintptr_t a0 = (uintptr_t)a, a1 = a0 + abytes;
  uintptr_t b0 = (uintptr_t)b, b1 = b0 + bbytes;
  return a0 < b1 && b0 < a1;
}

/* ---- public API ---------------------------------------------------------- */

tvdb_status_t tvdb_mesh_simplify_ex(const tvdb_triangle_mesh *in,
                                     const tvdb_simplify_options_t *options,
                                     tvdb_triangle_mesh *out,
                                     tvdb_arena_allocator_t *arena,
                                     tvdb_error_t *err) {
  if (!in || !options || !out || in == out ||
      (in->vertex_count && !in->vertices) ||
      (in->face_count && !in->faces) ||
      (out->vertex_capacity && !out->vertices) ||
      (out->face_capacity && !out->faces)) {
    simplify_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "mesh_simplify: invalid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t nv = in->vertex_count, nf = in->face_count;
  if (ranges_overlap(in->vertices, nv * sizeof(tvdb_vec3f),
                     out->vertices, out->vertex_capacity * sizeof(tvdb_vec3f)) ||
      ranges_overlap(in->faces, nf * sizeof(tvdb_triangle),
                     out->faces, out->face_capacity * sizeof(tvdb_triangle)) ||
      ranges_overlap(out->vertices, out->vertex_capacity * sizeof(tvdb_vec3f),
                     out->faces, out->face_capacity * sizeof(tvdb_triangle))) {
    simplify_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "mesh_simplify: aliasing output");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  for (size_t f = 0; f < nf; ++f) {
    uint32_t a = in->faces[f].v0, b = in->faces[f].v1, c = in->faces[f].v2;
    if (a >= nv || b >= nv || c >= nv || a == b || b == c || a == c) {
      simplify_set_error(err, TVDB_ERROR_INVALID_DATA, "mesh_simplify: invalid face index");
      return TVDB_ERROR_INVALID_DATA;
    }
  }

  size_t mark = arena ? arena->current_offset : 0;
  tvdb_status_t st = TVDB_OK;
  quadric_t *quad = NULL;
  double *pos = NULL;
  bool *boundary = NULL, *alive = NULL, *dead = NULL;
  uint32_t *faces = NULL;
  uint64_t *edge_keys = NULL;
  candidate_t *cands = NULL;
  uint32_t *map = NULL;
  tvdb_vec3f *newv = NULL;
  tvdb_triangle *newf = NULL;

  /* Trivial case: copy the input. */
  if (options->target_faces >= nf) {
    quad = (quadric_t *)calloc(nv ? nv : 1, sizeof(quadric_t));
    pos = (double *)malloc((nv * 3 + 1) * sizeof(double));
    if (!quad || !pos) { st = TVDB_ERROR_OUT_OF_MEMORY; goto fail; }
    (void)quad;
    newv = (tvdb_vec3f *)(arena ? tvdb_arena_alloc(arena, (nv ? nv : 1) * sizeof(tvdb_vec3f))
                                : malloc((nv ? nv : 1) * sizeof(tvdb_vec3f)));
    newf = (tvdb_triangle *)(arena ? tvdb_arena_alloc(arena, (nf ? nf : 1) * sizeof(tvdb_triangle))
                                   : malloc((nf ? nf : 1) * sizeof(tvdb_triangle)));
    if (!newv || !newf) { st = TVDB_ERROR_OUT_OF_MEMORY; goto fail; }
    memcpy(newv, in->vertices, nv * sizeof(tvdb_vec3f));
    memcpy(newf, in->faces, nf * sizeof(tvdb_triangle));
    if (!arena) { free(out->vertices); free(out->faces); }
    out->vertices = newv; out->vertex_count = nv; out->vertex_capacity = nv;
    out->faces = newf; out->face_count = nf; out->face_capacity = nf;
    newv = NULL; newf = NULL;
    goto done;
  }

  quad = (quadric_t *)calloc(nv ? nv : 1, sizeof(quadric_t));
  pos = (double *)malloc((nv * 3 + 1) * sizeof(double));
  boundary = (bool *)calloc(nv ? nv : 1, sizeof(bool));
  alive = (bool *)malloc((nv ? nv : 1) * sizeof(bool));
  faces = (uint32_t *)malloc((nf * 3 + 1) * sizeof(uint32_t));
  dead = (bool *)calloc(nf ? nf : 1, sizeof(bool));
  edge_keys = (uint64_t *)malloc((nf * 3 + 1) * sizeof(uint64_t));
  cands = (candidate_t *)malloc((nf * 3 + 1) * sizeof(candidate_t));
  map = (uint32_t *)malloc((nv ? nv : 1) * sizeof(uint32_t));
  if (!quad || !pos || !boundary || !alive || !faces || !dead || !edge_keys ||
      !cands || !map) { st = TVDB_ERROR_OUT_OF_MEMORY; goto fail; }

  for (size_t i = 0; i < nv; ++i) {
    pos[3 * i] = in->vertices[i].x;
    pos[3 * i + 1] = in->vertices[i].y;
    pos[3 * i + 2] = in->vertices[i].z;
    alive[i] = true;
  }
  for (size_t f = 0; f < nf; ++f) {
    faces[3 * f] = in->faces[f].v0;
    faces[3 * f + 1] = in->faces[f].v1;
    faces[3 * f + 2] = in->faces[f].v2;
    double p[3][3];
    for (int k = 0; k < 3; ++k) {
      uint32_t vi = faces[3 * f + k];
      p[k][0] = pos[3 * vi]; p[k][1] = pos[3 * vi + 1]; p[k][2] = pos[3 * vi + 2];
    }
    double e1[3] = {p[1][0] - p[0][0], p[1][1] - p[0][1], p[1][2] - p[0][2]};
    double e2[3] = {p[2][0] - p[0][0], p[2][1] - p[0][1], p[2][2] - p[0][2]};
    double n[3] = {e1[1] * e2[2] - e1[2] * e2[1],
                   e1[2] * e2[0] - e1[0] * e2[2],
                   e1[0] * e2[1] - e1[1] * e2[0]};
    /* Scale by 1/|n|² rather than dividing n by sqrt(|n|²): the cost is the
       same squared plane distance, and it stays rational for integer inputs. */
    double len2 = n[0] * n[0] + n[1] * n[1] + n[2] * n[2];
    if (!(len2 > 1e-30)) continue;
    double d = n[0] * p[0][0] + n[1] * p[0][1] + n[2] * p[0][2];
    quadric_t q;
    quadric_plane(&q, n, d);
    for (int i = 0; i < 6; ++i) q.a[i] /= len2;
    for (int i = 0; i < 3; ++i) q.b[i] /= len2;
    q.c /= len2;
    for (int k = 0; k < 3; ++k) quadric_add(&quad[faces[3 * f + k]], &q);
  }

  /* Boundary edges occur exactly once as undirected edges. */
  size_t ne = 0;
  for (size_t f = 0; f < nf; ++f)
    for (int e = 0; e < 3; ++e)
      edge_keys[ne++] = edge_key(faces[3 * f + e], faces[3 * f + (e + 1) % 3]);
  qsort(edge_keys, ne, sizeof(uint64_t), cmp_u64);
  for (size_t k = 0; k < ne; ++k) {
    bool single = (k == 0 || edge_keys[k] != edge_keys[k - 1]) &&
                  (k + 1 == ne || edge_keys[k] != edge_keys[k + 1]);
    if (single) {
      boundary[edge_keys[k] >> 32] = true;
      boundary[edge_keys[k] & 0xffffffffu] = true;
    }
  }

  /* Candidate collapses: one per undirected edge, visited in sorted-key order. */
  size_t nc = 0;
  for (size_t e = 0; e < ne; ++e) {
    if (e && edge_keys[e] == edge_keys[e - 1]) continue;
    uint32_t a = (uint32_t)(edge_keys[e] >> 32);
    uint32_t b = (uint32_t)(edge_keys[e] & 0xffffffffu);
    if (options->preserve_boundary && (boundary[a] || boundary[b])) continue;
    if (!link_ok(faces, nf, dead, a, b)) continue;
    double mid[3] = {(pos[3 * a] + pos[3 * b]) * 0.5,
                     (pos[3 * a + 1] + pos[3 * b + 1]) * 0.5,
                     (pos[3 * a + 2] + pos[3 * b + 2]) * 0.5};
    quadric_t sum;
    quadric_zero(&sum);
    quadric_add(&sum, &quad[a]);
    quadric_add(&sum, &quad[b]);
    double cost = quadric_eval(&sum, mid);
    if (!isfinite(cost)) continue;
    cands[nc].cost = cost;
    cands[nc].i = a;
    cands[nc].j = b;
    ++nc;
  }
  qsort(cands, nc, sizeof(candidate_t), cmp_candidate);

  size_t live_faces = nf;
  for (size_t k = 0; k < nc && live_faces > options->target_faces; ++k) {
    uint32_t a = cands[k].i, b = cands[k].j;
    if (!alive[a] || !alive[b]) continue;
    if (!link_ok(faces, nf, dead, a, b)) continue;
    for (int d = 0; d < 3; ++d)
      pos[3 * a + d] = (pos[3 * a + d] + pos[3 * b + d]) * 0.5;
    alive[b] = false;
    for (size_t f = 0; f < nf; ++f) {
      if (dead[f]) continue;
      for (int d = 0; d < 3; ++d)
        if (faces[3 * f + d] == b) faces[3 * f + d] = a;
      bool drop = face_degenerate(faces + 3 * f);
      if (!drop)
        for (size_t g = 0; g < f; ++g)
          if (!dead[g] && face_equal(faces + 3 * g, faces + 3 * f)) { drop = true; break; }
      if (drop) { dead[f] = true; --live_faces; }
    }
  }

  if (options->verify_watertight && live_faces && !closed_mesh(faces, nf, dead)) {
    simplify_set_error(err, TVDB_ERROR_INVALID_DATA,
                    "mesh_simplify: collapsed mesh is not a closed manifold");
    st = TVDB_ERROR_INVALID_DATA;
    goto fail;
  }

  /* Compact the surviving vertices/faces in increasing original index order. */
  uint32_t nv_new = 0;
  for (size_t i = 0; i < nv; ++i) if (alive[i]) map[i] = nv_new++;
  newv = (tvdb_vec3f *)(arena ? tvdb_arena_alloc(arena, (nv_new ? nv_new : 1) * sizeof(tvdb_vec3f))
                              : malloc((nv_new ? nv_new : 1) * sizeof(tvdb_vec3f)));
  newf = (tvdb_triangle *)(arena ? tvdb_arena_alloc(arena, (live_faces ? live_faces : 1) * sizeof(tvdb_triangle))
                                 : malloc((live_faces ? live_faces : 1) * sizeof(tvdb_triangle)));
  if (!newv || !newf) { st = TVDB_ERROR_OUT_OF_MEMORY; goto fail; }
  for (size_t i = 0; i < nv; ++i)
    if (alive[i]) {
      newv[map[i]].x = (float)pos[3 * i];
      newv[map[i]].y = (float)pos[3 * i + 1];
      newv[map[i]].z = (float)pos[3 * i + 2];
    }
  uint32_t nf_new = 0;
  for (size_t f = 0; f < nf; ++f)
    if (!dead[f]) {
      newf[nf_new].v0 = map[faces[3 * f]];
      newf[nf_new].v1 = map[faces[3 * f + 1]];
      newf[nf_new].v2 = map[faces[3 * f + 2]];
      ++nf_new;
    }
  if (!arena) { free(out->vertices); free(out->faces); }
  out->vertices = newv; out->vertex_count = nv_new; out->vertex_capacity = nv_new;
  out->faces = newf; out->face_count = nf_new; out->face_capacity = nf_new;
  newv = NULL; newf = NULL;

done:
  if (arena && arena->current_offset < mark) arena->current_offset = mark;
  free(quad); free(pos); free(boundary); free(alive); free(faces); free(dead);
  free(edge_keys); free(cands); free(map); free(newv); free(newf);
  return st;

fail:
  if (arena) arena->current_offset = mark;
  free(quad); free(pos); free(boundary); free(alive); free(faces); free(dead);
  free(edge_keys); free(cands); free(map); free(newv); free(newf);
  return st;
}

bool tvdb_mesh_simplify(const tvdb_triangle_mesh *in, size_t target_faces,
                         tvdb_triangle_mesh *out, tvdb_arena_allocator_t *arena) {
  tvdb_simplify_options_t opt = {target_faces, true, true};
  return tvdb_mesh_simplify_ex(in, &opt, out, arena, NULL) == TVDB_OK;
}
