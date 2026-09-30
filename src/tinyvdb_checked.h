#pragma once

/* Private checked arithmetic shared by allocation and coordinate paths. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <limits.h>

static inline bool tvdb_size_mul(size_t a, size_t b, size_t *out) {
    if (b && a > SIZE_MAX / b) return false;
    *out = a * b;
    return true;
}

static inline bool tvdb_grid_bytes(int nx, int ny, int nz, size_t element_bytes,
                                   size_t *out) {
    size_t n;
    return nx > 0 && ny > 0 && nz > 0 &&
           tvdb_size_mul((size_t)nx, (size_t)ny, &n) &&
           tvdb_size_mul(n, (size_t)nz, &n) &&
           tvdb_size_mul(n, element_bytes, out);
}

static inline bool tvdb_hash_capacity(size_t count, size_t factor, size_t *out) {
    size_t need;
    if (!tvdb_size_mul(count, factor, &need) || need > SIZE_MAX - 16) return false;
    need += 16;
    size_t cap = 16;
    while (cap < need) {
        if (cap > SIZE_MAX / 2) return false;
        cap *= 2;
    }
    *out = cap;
    return true;
}

static inline bool tvdb_coord_offset(int x, int y, int z, int dx, int dy, int dz,
                                     int *ox, int *oy, int *oz) {
    int64_t a = (int64_t)x + dx, b = (int64_t)y + dy, c = (int64_t)z + dz;
    if (a < INT32_MIN || a > INT32_MAX || b < INT32_MIN || b > INT32_MAX ||
        c < INT32_MIN || c > INT32_MAX) return false;
    *ox = (int)a; *oy = (int)b; *oz = (int)c;
    return true;
}
