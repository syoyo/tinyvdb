/* Inject failures into every conversion-owned heap allocation. Native worker
 * creation has separate fault coverage in test_thread_pool_failure. */
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef union {
    max_align_t alignment;
    struct {
        size_t bytes;
    } info;
} block_header;
static size_t calls, fail_at, live, bytes, peak;
static void *fault_malloc(size_t n) {
    if (++calls == fail_at || n > SIZE_MAX - sizeof(block_header))
        return NULL;
    block_header *h = malloc(sizeof(*h) + n);
    if (!h)
        return NULL;
    h->info.bytes = n;
    ++live;
    bytes += n;
    if (bytes > peak)
        peak = bytes;
    return h + 1;
}
static void fault_free(void *p) {
    if (p) {
        block_header *h = (block_header *)p - 1;
        bytes -= h->info.bytes;
        --live;
        free(h);
    }
}
static void *fault_calloc(size_t n, size_t s) {
    if (s && n > SIZE_MAX / s)
        return NULL;
    void *p = fault_malloc(n * s);
    if (p)
        memset(p, 0, n * s);
    return p;
}
static void *fault_realloc(void *p, size_t n) {
    void *q = fault_malloc(n);
    if (!q)
        return NULL;
    if (p) {
        size_t old = ((block_header *)p - 1)->info.bytes;
        memcpy(q, p, old < n ? old : n);
        fault_free(p);
    }
    return q;
}
#define malloc fault_malloc
#define calloc fault_calloc
#define realloc fault_realloc
#define free fault_free
#include "../src/tinyvdb_mesh.c"
#undef malloc
#undef calloc
#undef realloc
#undef free
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "line %d: %s\n", __LINE__, #x);                                        \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)
static void release(tvdb_triangle_mesh *m) {
    fault_free(m->vertices);
    fault_free(m->faces);
    memset(m, 0, sizeof(*m));
}
int main(void) {
    tvdb_thread_pool_t *pool = NULL;
    CHECK(tvdb_thread_pool_create(1, &pool, NULL) == TVDB_OK);
    int n = 24;
    size_t samples = (size_t)n * n * n;
    float *field = malloc(samples * 4);
    CHECK(field);
    for (size_t i = 0; i < samples; ++i)
        field[i] = ((i % n + i / n % n + i / (n * n)) & 1) ? -1 : 1;
    tvdb_dense_grid g = {n, n, n, 0, 0, 0, 1, field};
    tvdb_triangle_mesh source = {0};
    calls = 0;
    CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_OUTWARD, pool, &source, NULL, NULL) ==
          TVDB_OK);
    size_t allocations = calls, base_live = live, base_bytes = bytes;
    CHECK(peak - base_bytes <= (size_t)20 * n * n + (size_t)n * sizeof(mesh_mc_count));
    /* All count/cache/output allocation failures preserve an existing prefix. */
    for (size_t fail = 1; fail <= allocations; ++fail) {
        tvdb_triangle_mesh out = {0};
        out.vertices = fault_malloc(sizeof(tvdb_vec3f));
        out.faces = fault_malloc(sizeof(tvdb_triangle));
        out.vertex_count = out.vertex_capacity = out.face_count = out.face_capacity = 1;
        out.vertices[0] = (tvdb_vec3f){8, 9, 10};
        out.faces[0] = (tvdb_triangle){0, 0, 0};
        tvdb_triangle_mesh saved = out;
        calls = 0;
        fail_at = fail;
        CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, pool, &out, NULL, NULL) ==
              TVDB_ERROR_OUT_OF_MEMORY);
        CHECK(!memcmp(&out, &saved, sizeof(out)) && out.vertices[0].y == 9 && out.faces[0].v1 == 0);
        fail_at = 0;
        release(&out);
        CHECK(live == base_live && bytes == base_bytes);
    }
    tvdb_mesh_sdf_t *w = NULL;
    calls = 0;
    CHECK(tvdb_mesh_sdf_create(&source, &w, NULL) == TVDB_OK);
    allocations = calls;
    tvdb_mesh_sdf_destroy(w);
    CHECK(allocations > 5); /* includes multiple BVH node-array reallocations */
    for (size_t fail = 1; fail <= allocations; ++fail) {
        calls = 0;
        fail_at = fail;
        w = (void *)1;
        CHECK(tvdb_mesh_sdf_create(&source, &w, NULL) == TVDB_ERROR_OUT_OF_MEMORY && !w);
        CHECK(live == base_live && bytes == base_bytes);
    }
    fail_at = 0;
    CHECK(tvdb_mesh_sdf_create(&source, &w, NULL) == TVDB_OK);
    size_t workspace_live = live, workspace_bytes = bytes;
    tvdb_dense_grid out = {1, 1, 1, 0, 0, 0, 1, NULL};
    out.data = fault_malloc(4);
    out.data[0] = 123;
    tvdb_dense_grid saved = out;
    calls = 0;
    fail_at = 1;
    CHECK(tvdb_mesh_sdf_generate(w, 1, 1, pool, &out, NULL, NULL) == TVDB_ERROR_OUT_OF_MEMORY);
    CHECK(!memcmp(&out, &saved, sizeof(out)) && out.data[0] == 123);
    fail_at = 0;
    fault_free(out.data);
    CHECK(live == workspace_live && bytes == workspace_bytes);
    /* A fresh vertex allocation fits, but face allocation fails: roll back the
       arena including its alignment padding, before the caller retries. */
    char buffer[64];
    tvdb_arena_allocator_t arena = {buffer, sizeof(buffer), 3};
    float plane[8] = {-1, 1, -1, 1, -1, 1, -1, 1};
    tvdb_dense_grid tiny = {2, 2, 2, 0, 0, 0, 1, plane};
    tvdb_triangle_mesh mesh = {0};
    CHECK(tvdb_sdf_to_mesh_ex(&tiny, 0, TVDB_MESH_WINDING_TABLE, pool, &mesh, &arena, NULL) ==
          TVDB_ERROR_OUT_OF_MEMORY);
    CHECK(arena.current_offset == 3 && !mesh.vertices && !mesh.faces && !mesh.vertex_count);
    arena.current_offset = 3;
    out = (tvdb_dense_grid){0};
    CHECK(tvdb_mesh_sdf_generate(w, 1, 1, pool, &out, &arena, NULL) == TVDB_ERROR_OUT_OF_MEMORY);
    CHECK(arena.current_offset == 3 && !out.data);
    tvdb_mesh_sdf_destroy(w);
    CHECK(live == base_live && bytes == base_bytes);
    /* Successful arena conversion retains exactly the output; caches are heap scratch. */
    size_t output_bytes =
        source.vertex_count * sizeof(tvdb_vec3f) + source.face_count * sizeof(tvdb_triangle);
    void *storage = malloc(output_bytes + 16);
    CHECK(storage);
    arena = (tvdb_arena_allocator_t){storage, output_bytes + 16, 0};
    CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, pool, &mesh, &arena, NULL) ==
          TVDB_OK);
    CHECK(arena.current_offset <= output_bytes + 7 && live == base_live && bytes == base_bytes);
    free(storage);
    release(&source);
    free(field);
    tvdb_thread_pool_destroy(pool);
    CHECK(!live && !bytes);
    return 0;
}
