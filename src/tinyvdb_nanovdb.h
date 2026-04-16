/*
 * TinyVDB NanoVDB I/O — NanoVDB file format support for TinyVDB.
 *
 * Copyright (c) 2026 - Present Syoyo Fujita
 * Based on NanoVDB by Ken Museth
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NanoVDB (by Ken Museth) is a read-only sparse GPU (and CPU) friendly
 * data structure. This module provides read/write support for NanoVDB files.
 *
 * Usage:
 *   #define TINYVDB_NANOVDB_IMPLEMENTATION
 *   #include "tinyvdb_nanovdb.h"
 */
#ifndef TINYVDB_NANOVDB_H_
#define TINYVDB_NANOVDB_H_

#include <stdint.h>
#include <stddef.h>

/* Forward declare types from tinyvdb_io.h to avoid circular dependency */
#ifndef TVDB_STATUS_T_DEFINED
#define TVDB_STATUS_T_DEFINED
typedef enum tvdb_status {
    TVDB_OK = 0,
    TVDB_ERROR_INVALID_FILE,
    TVDB_ERROR_INVALID_HEADER,
    TVDB_ERROR_INVALID_DATA,
    TVDB_ERROR_INVALID_ARGUMENT,
    TVDB_ERROR_UNSUPPORTED_VERSION,
    TVDB_ERROR_UNSUPPORTED_GRID_TYPE,
    TVDB_ERROR_UNSUPPORTED_COMPRESSION,
    TVDB_ERROR_UNSUPPORTED_TRANSFORM,
    TVDB_ERROR_DECOMPRESSION_FAILED,
    TVDB_ERROR_OUT_OF_MEMORY,
    TVDB_ERROR_IO,
    TVDB_ERROR_MMAP_FAILED,
    TVDB_ERROR_PATH_CONVERSION,
    TVDB_ERROR_UNIMPLEMENTED
} tvdb_status_t;

typedef struct tvdb_error {
    tvdb_status_t status;
    char          message[512];
    uint64_t      byte_offset;
    int32_t       grid_index;
} tvdb_error_t;

typedef struct tvdb_allocator {
    void *(*malloc_fn)(size_t size, void *user_ctx);
    void *(*realloc_fn)(void *ptr, size_t old_size, size_t new_size,
                        void *user_ctx);
    void (*free_fn)(void *ptr, size_t size, void *user_ctx);
    void *user_ctx;
} tvdb_allocator_t;

#define TVDB_MAX_ERROR_MSG 512
#endif

#ifdef __cplusplus
extern "C" {
#endif

/* ========================================================================== */
/*  Constants                                                                 */
/* ========================================================================== */

/* NanoVDB magic numbers */
#define TVDB_NANOVDB_MAGIC_FILE 0x324244566f6e614eULL  /* "NanoVDB2" */
#define TVDB_NANOVDB_MAGIC_GRID 0x314244566f6e614eULL  /* "NanoVDB1" */
#define TVDB_NANOVDB_MAGIC_NUMB 0x304244566f6e614eULL  /* "NanoVDB0" */

#define TVDB_NANOVDB_VERSION_MAJOR 32
#define TVDB_NANOVDB_VERSION_MINOR 6
#define TVDB_NANOVDB_VERSION_PATCH 0

/* Memory alignment (32 bytes) */
#define TVDB_NANOVDB_DATA_ALIGNMENT 32

/* Node dimensions (fixed for NanoVDB) */
#define TVDB_NANOVDB_LEAF_DIM 8
#define TVDB_NANOVDB_LEAF_LOG2DIM 3
#define TVDB_NANOVDB_LEAF_VOXELS 512  /* 8^3 */
#define TVDB_NANOVDB_INTERIOR_DIM 16
#define TVDB_NANOVDB_INTERIOR_LOG2DIM 4
#define TVDB_NANOVDB_INTERIOR_TILES 4096  /* 16^3 */
#define TVDB_NANOVDB_UPPER_DIM 32
#define TVDB_NANOVDB_UPPER_LOG2DIM 5
#define TVDB_NANOVDB_UPPER_TILES 32768  /* 32^3 */

/* ========================================================================== */
/*  Enums                                                                     */
/* ========================================================================== */

typedef enum tvdb_nanovdb_codec {
    TVDB_NANOVDB_CODEC_NONE = 0,
    TVDB_NANOVDB_CODEC_ZIP  = 1,
    TVDB_NANOVDB_CODEC_BLOSC = 2
} tvdb_nanovdb_codec_t;

typedef enum tvdb_nanovdb_grid_type {
    TVDB_NANOVDB_GRID_TYPE_UNKNOWN = 0,
    TVDB_NANOVDB_GRID_TYPE_FLOAT   = 1,
    TVDB_NANOVDB_GRID_TYPE_DOUBLE  = 2,
    TVDB_NANOVDB_GRID_TYPE_INT16   = 3,
    TVDB_NANOVDB_GRID_TYPE_INT32   = 4,
    TVDB_NANOVDB_GRID_TYPE_INT64   = 5,
    TVDB_NANOVDB_GRID_TYPE_VEC3F   = 6,
    TVDB_NANOVDB_GRID_TYPE_VEC3D   = 7,
    TVDB_NANOVDB_GRID_TYPE_MASK    = 8,
    TVDB_NANOVDB_GRID_TYPE_HALF    = 9,
    TVDB_NANOVDB_GRID_TYPE_UINT32  = 10,
    TVDB_NANOVDB_GRID_TYPE_BOOLEAN = 11,
    TVDB_NANOVDB_GRID_TYPE_RGBA8   = 12,
    TVDB_NANOVDB_GRID_TYPE_FP4     = 13,
    TVDB_NANOVDB_GRID_TYPE_FP8     = 14,
    TVDB_NANOVDB_GRID_TYPE_FP16    = 15,
    TVDB_NANOVDB_GRID_TYPE_FPN     = 16,
    TVDB_NANOVDB_GRID_TYPE_VEC4F   = 17,
    TVDB_NANOVDB_GRID_TYPE_VEC4D   = 18,
    TVDB_NANOVDB_GRID_TYPE_INDEX   = 19,
    TVDB_NANOVDB_GRID_TYPE_ONINDEX = 20,
    TVDB_NANOVDB_GRID_TYPE_POINT_INDEX = 23,
    TVDB_NANOVDB_GRID_TYPE_VEC3U8  = 24,
    TVDB_NANOVDB_GRID_TYPE_VEC3U16 = 25,
    TVDB_NANOVDB_GRID_TYPE_UINT8   = 26
} tvdb_nanovdb_grid_type_t;

typedef enum tvdb_nanovdb_grid_class {
    TVDB_NANOVDB_GRID_CLASS_UNKNOWN    = 0,
    TVDB_NANOVDB_GRID_CLASS_LEVEL_SET  = 1,
    TVDB_NANOVDB_GRID_CLASS_FOG_VOLUME = 2,
    TVDB_NANOVDB_GRID_CLASS_STAGGERED   = 3,
    TVDB_NANOVDB_GRID_CLASS_COLLISION   = 4,
    TVDB_NANOVDB_GRID_CLASS_POINT_INDEX = 5,
    TVDB_NANOVDB_GRID_CLASS_POINT_DATA  = 6,
    TVDB_NANOVDB_GRID_CLASS_STUB        = 7,
    TVDB_NANOVDB_GRID_CLASS_MACCABE    = 8,
    TVDB_NANOVDB_GRID_CLASS_SDF_FUZZY  = 9
} tvdb_nanovdb_grid_class_t;

typedef enum tvdb_nanovdb_checksum_mode {
    TVDB_NANOVDB_CHECKSUM_NONE      = 0,
    TVDB_NANOVDB_CHECKSUM_EASTWOOD  = 1,
    TVDB_NANOVDB_CHECKSUM_DEFAULT   = 2
} tvdb_nanovdb_checksum_mode_t;

/* ========================================================================== */
/*  Structures                                                                 */
/* ========================================================================== */

/* File header (16 bytes) */
typedef struct tvdb_nanovdb_file_header {
    uint64_t magic;
    uint32_t version;
    uint16_t grid_count;
    uint16_t codec;
} tvdb_nanovdb_file_header_t;

/* File metadata (176 bytes) */
typedef struct tvdb_nanovdb_file_meta {
    uint64_t grid_size;
    uint64_t file_size;
    uint64_t name_key;
    uint64_t voxel_count;
    uint32_t grid_type;
    uint32_t grid_class;
    double   world_bbox_min[3];
    double   world_bbox_max[3];
    int32_t  index_bbox_min[3];
    int32_t  index_bbox_max[3];
    double   voxel_size[3];
    uint32_t name_size;
    uint32_t node_count[4];
    uint32_t tile_count[3];
    uint16_t codec;
    uint16_t blind_data_count;
    uint32_t version;
} tvdb_nanovdb_file_meta_t;

/* Grid data (672 bytes, 32-byte aligned) */
typedef struct tvdb_nanovdb_grid_data {
    uint64_t magic;
    uint64_t checksum;
    uint32_t version;
    uint32_t flags;
    uint32_t grid_index;
    uint32_t grid_count;
    uint64_t grid_size;
    char     grid_name[256];
    double   map[12];
    double   world_bbox_min[3];
    double   world_bbox_max[3];
    double   voxel_size[3];
    uint32_t grid_class;
    uint32_t grid_type;
    int64_t  blind_metadata_offset;
    uint32_t blind_metadata_count;
    uint32_t data0;
    uint64_t data1;
    uint64_t data2;
} tvdb_nanovdb_grid_data_t;

/* Tree data (64 bytes, 32-byte aligned) */
typedef struct tvdb_nanovdb_tree_data {
    int64_t  node_offset[4];
    uint32_t node_count[3];
    uint32_t tile_count[3];
    uint64_t voxel_count;
} tvdb_nanovdb_tree_data_t;

/* Node types (used for traversal) */
typedef enum tvdb_nanovdb_node_type {
    TVDB_NANOVDB_NODE_LEAF   = 0,
    TVDB_NANOVDB_NODE_LOWER  = 1,
    TVDB_NANOVDB_NODE_UPPER  = 2,
    TVDB_NANOVDB_NODE_ROOT   = 3
} tvdb_nanovdb_node_type_t;

/* Blind metadata entry (40 bytes) */
typedef struct tvdb_nanovdb_blind_meta {
    int64_t  byte_offset;
    uint64_t byte_size;
    uint64_t name_key;
    uint32_t value_count;
    uint32_t grid_type;
    uint32_t semantic;
    uint32_t flags;
} tvdb_nanovdb_blind_meta_t;

/* Grid structure for accessing NanoVDB data */
typedef struct tvdb_nanovdb_grid {
    char     *name;
    uint64_t  size;
    uint32_t  grid_type;
    uint32_t  grid_class;
    double    voxel_size[3];
    double    world_bbox_min[3];
    double    world_bbox_max[3];
    int32_t   index_bbox_min[3];
    int32_t   index_bbox_max[3];
    uint64_t  active_voxel_count;
    uint32_t  node_count[4];
    uint32_t  tile_count[3];

    /* Raw data pointers (relative to grid start) */
    int64_t   tree_data_offset;
    int64_t   root_data_offset;
    int64_t   leaf_data_offset;
    int64_t   lower_data_offset;
    int64_t   upper_data_offset;

    uint8_t  *data;
    int       owns_data;
} tvdb_nanovdb_grid_t;

/* Top-level file context */
typedef struct tvdb_nanovdb_file {
    uint32_t               version;
    uint16_t              grid_count;
    uint16_t              codec;
    tvdb_nanovdb_grid_t  *grids;
    size_t                num_grids;
    uint64_t              file_size;
    const uint8_t        *mmap_data;
    uint8_t              *buffer;
    tvdb_allocator_t      alloc;
} tvdb_nanovdb_file_t;

/* ========================================================================== */
/*  Public API                                                                */
/* ========================================================================== */

/* File operations */
tvdb_status_t tvdb_nanovdb_file_open(tvdb_nanovdb_file_t *file,
                                      const char *filepath_utf8,
                                      const tvdb_allocator_t *alloc,
                                      tvdb_error_t *err);

tvdb_status_t tvdb_nanovdb_file_open_memory(tvdb_nanovdb_file_t *file,
                                            const uint8_t *data,
                                            size_t data_len,
                                            const tvdb_allocator_t *alloc,
                                            tvdb_error_t *err);

void tvdb_nanovdb_file_close(tvdb_nanovdb_file_t *file);

/* Grid access */
size_t        tvdb_nanovdb_grid_count(const tvdb_nanovdb_file_t *file);
const char   *tvdb_nanovdb_grid_name(const tvdb_nanovdb_file_t *file, size_t idx);
uint32_t      tvdb_nanovdb_grid_type(const tvdb_nanovdb_file_t *file, size_t idx);
uint32_t      tvdb_nanovdb_grid_class(const tvdb_nanovdb_file_t *file, size_t idx);
double        tvdb_nanovdb_grid_voxel_size(const tvdb_nanovdb_file_t *file, size_t idx, int axis);

/* Value access */
float   tvdb_nanovdb_get_voxel_f(const tvdb_nanovdb_grid_t *grid, int x, int y, int z);
double  tvdb_nanovdb_get_voxel_d(const tvdb_nanovdb_grid_t *grid, int x, int y, int z);
int     tvdb_nanovdb_is_voxel_active(const tvdb_nanovdb_grid_t *grid, int x, int y, int z);

/* Writing API */
tvdb_status_t tvdb_nanovdb_write_to_memory(const tvdb_nanovdb_file_t *file,
                                            uint32_t compression_flags,
                                            uint8_t **out_data,
                                            size_t *out_size,
                                            tvdb_error_t *err);

tvdb_status_t tvdb_nanovdb_file_save(const tvdb_nanovdb_file_t *file,
                                      const char *filepath_utf8,
                                      uint32_t compression_flags,
                                      int use_mmap,
                                      tvdb_error_t *err);

/* Grid creation API */
uint64_t tvdb_nanovdb_leaf_node_size(uint32_t grid_type);
uint64_t tvdb_nanovdb_lower_node_size(uint32_t grid_type);
uint64_t tvdb_nanovdb_upper_node_size(uint32_t grid_type);
uint64_t tvdb_nanovdb_root_tile_size(void);

tvdb_status_t tvdb_nanovdb_create_grid(tvdb_nanovdb_grid_t *grid,
                                       const char *name,
                                       uint32_t grid_type,
                                       uint32_t grid_class,
                                       int32_t min_coord[3],
                                       int32_t max_coord[3],
                                       const tvdb_allocator_t *alloc,
                                       tvdb_error_t *err);

void tvdb_nanovdb_destroy_grid(tvdb_nanovdb_grid_t *grid,
                                const tvdb_allocator_t *alloc);

/* Utility */
const char *tvdb_nanovdb_grid_type_name(uint32_t grid_type);
const char *tvdb_nanovdb_grid_class_name(uint32_t grid_class);
int          tvdb_nanovdb_is_big_endian_file(const tvdb_nanovdb_file_t *file);
uint32_t     tvdb_nanovdb_value_size(uint32_t grid_type);

#ifdef __cplusplus
}
#endif

/* ========================================================================== */
/*  IMPLEMENTATION                                                            */
/* ========================================================================== */

#ifdef TINYVDB_NANOVDB_IMPLEMENTATION

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#ifndef TVDB_ASSERT
#define TVDB_ASSERT(x) assert(x)
#endif

#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif

#if !defined(TVDB_NO_MMAP)
#  if defined(_WIN32)
#    include <windows.h>
#  else
#    include <sys/mman.h>
#    include <sys/stat.h>
#    include <fcntl.h>
#    include <unistd.h>
#  endif
#endif

#include "lz4.h"

#if !defined(TVDB_USE_SYSTEM_ZLIB)
#  ifndef MINIZ_NO_STDIO
#    define MINIZ_NO_STDIO
#  endif
#  include "miniz.h"
#else
#  include <zlib.h>
#endif

/* ========================================================================== */
/*  Internal helpers                                                          */
/* ========================================================================== */

static uint16_t tvdb__nnvdb_swap16(uint16_t v) {
    return (uint16_t)((v >> 8) | (v << 8));
}

static uint32_t tvdb__nnvdb_swap32(uint32_t v) {
    return ((v >> 24) & 0x000000FF) |
           ((v >> 8)  & 0x0000FF00) |
           ((v << 8)  & 0x00FF0000) |
           ((v << 24) & 0xFF000000);
}

static uint64_t tvdb__nnvdb_swap64(uint64_t v) {
    return ((v >> 56) & 0x00000000000000FFULL) |
           ((v >> 40) & 0x000000000000FF00ULL) |
           ((v >> 24) & 0x0000000000FF0000ULL) |
           ((v >> 8)  & 0x00000000FF000000ULL) |
           ((v << 8)  & 0x000000FF00000000ULL) |
           ((v << 24) & 0x0000FF0000000000ULL) |
           ((v << 40) & 0x00FF000000000000ULL) |
           ((v << 56) & 0xFF00000000000000ULL);
}

static double tvdb__nnvdb_swap_double(double v) {
    union { double d; uint64_t u; } u;
    u.d = v;
    u.u = tvdb__nnvdb_swap64(u.u);
    return u.d;
}

static int tvdb__nnvdb_is_little_endian(void) {
    const uint16_t x = 1;
    return ((const uint8_t *)&x)[0] == 1;
}

static void tvdb__nnvdb_set_error(tvdb_error_t *err, tvdb_status_t status,
                                  const char *msg) {
    if (!err) return;
    err->status = status;
    if (msg) {
        size_t len = strlen(msg);
        if (len >= TVDB_MAX_ERROR_MSG) len = TVDB_MAX_ERROR_MSG - 1;
        memcpy(err->message, msg, len);
        err->message[len] = '\0';
    } else {
        err->message[0] = '\0';
    }
}

/* ========================================================================== */
/*  Stream reader for NanoVDB                                                 */
/* ========================================================================== */

typedef struct {
    const uint8_t *data;
    uint64_t       pos;
    uint64_t       length;
    int            swap_endian;
} tvdb__nnvdb_sr_t;

static void tvdb__nnvdb_sr_init(tvdb__nnvdb_sr_t *sr, const uint8_t *data,
                                uint64_t length, int swap) {
    sr->data = data;
    sr->pos = 0;
    sr->length = length;
    sr->swap_endian = swap;
}

static int tvdb__nnvdb_sr_read(tvdb__nnvdb_sr_t *sr, size_t n, void *dst) {
    if (sr->pos + n > sr->length) return 0;
    memcpy(dst, sr->data + sr->pos, n);
    sr->pos += n;
    return 1;
}

static int tvdb__nnvdb_sr_seek(tvdb__nnvdb_sr_t *sr, uint64_t pos) {
    if (pos > sr->length) return 0;
    sr->pos = pos;
    return 1;
}

static int tvdb__nnvdb_sr_skip(tvdb__nnvdb_sr_t *sr, int64_t offset) {
    uint64_t new_pos = (offset < 0) ?
        (sr->pos < (uint64_t)(-offset) ? 0 : sr->pos + offset) :
        sr->pos + offset;
    if (new_pos > sr->length) return 0;
    sr->pos = new_pos;
    return 1;
}

static uint64_t tvdb__nnvdb_sr_pos(tvdb__nnvdb_sr_t *sr) {
    return sr->pos;
}

static uint8_t tvdb__nnvdb_sr_read_u8(tvdb__nnvdb_sr_t *sr) {
    uint8_t v = 0;
    tvdb__nnvdb_sr_read(sr, 1, &v);
    return v;
}

static uint16_t tvdb__nnvdb_sr_read_u16(tvdb__nnvdb_sr_t *sr) {
    uint16_t v = 0;
    tvdb__nnvdb_sr_read(sr, 2, &v);
    return sr->swap_endian ? tvdb__nnvdb_swap16(v) : v;
}

static uint32_t tvdb__nnvdb_sr_read_u32(tvdb__nnvdb_sr_t *sr) {
    uint32_t v = 0;
    tvdb__nnvdb_sr_read(sr, 4, &v);
    return sr->swap_endian ? tvdb__nnvdb_swap32(v) : v;
}

static uint64_t tvdb__nnvdb_sr_read_u64(tvdb__nnvdb_sr_t *sr) {
    uint64_t v = 0;
    tvdb__nnvdb_sr_read(sr, 8, &v);
    return sr->swap_endian ? tvdb__nnvdb_swap64(v) : v;
}

static int32_t tvdb__nnvdb_sr_read_i32(tvdb__nnvdb_sr_t *sr) {
    return (int32_t)tvdb__nnvdb_sr_read_u32(sr);
}

static int64_t tvdb__nnvdb_sr_read_i64(tvdb__nnvdb_sr_t *sr) {
    return (int64_t)tvdb__nnvdb_sr_read_u64(sr);
}

static double tvdb__nnvdb_sr_read_double(tvdb__nnvdb_sr_t *sr) {
    union { double d; uint64_t u; } v;
    v.u = tvdb__nnvdb_sr_read_u64(sr);
    return sr->swap_endian ? tvdb__nnvdb_swap_double(v.d) : v.d;
}

static void tvdb__nnvdb_sr_read_str(tvdb__nnvdb_sr_t *sr, size_t len,
                                    char *dst) {
    tvdb__nnvdb_sr_read(sr, len, dst);
    dst[len] = '\0';
}

/* ========================================================================== */
/*  Stream writer for NanoVDB                                                 */
/* ========================================================================== */

typedef struct {
    uint8_t  *data;
    uint64_t  pos;
    uint64_t  capacity;
    int       swap_endian;
} tvdb__nnvdb_sw_t;

static int tvdb__nnvdb_sw_init(tvdb__nnvdb_sw_t *sw, uint8_t *data,
                               uint64_t capacity) {
    sw->data = data;
    sw->pos = 0;
    sw->capacity = capacity;
    sw->swap_endian = 0;
    return 1;
}

static int tvdb__nnvdb_sw_ensure(tvdb__nnvdb_sw_t *sw, uint64_t needed) {
    (void)sw;
    (void)needed;
    return 1;
}

static int tvdb__nnvdb_sw_write(tvdb__nnvdb_sw_t *sw, size_t n,
                                const void *src) {
    if (sw->pos + n > sw->capacity) return 0;
    memcpy(sw->data + sw->pos, src, n);
    sw->pos += n;
    return 1;
}

static void tvdb__nnvdb_sw_write_u8(tvdb__nnvdb_sw_t *sw, uint8_t v) {
    tvdb__nnvdb_sw_write(sw, 1, &v);
}

static void tvdb__nnvdb_sw_write_u16(tvdb__nnvdb_sw_t *sw, uint16_t v) {
    if (sw->swap_endian) v = tvdb__nnvdb_swap16(v);
    tvdb__nnvdb_sw_write(sw, 2, &v);
}

static void tvdb__nnvdb_sw_write_u32(tvdb__nnvdb_sw_t *sw, uint32_t v) {
    if (sw->swap_endian) v = tvdb__nnvdb_swap32(v);
    tvdb__nnvdb_sw_write(sw, 4, &v);
}

static void tvdb__nnvdb_sw_write_u64(tvdb__nnvdb_sw_t *sw, uint64_t v) {
    if (sw->swap_endian) v = tvdb__nnvdb_swap64(v);
    tvdb__nnvdb_sw_write(sw, 8, &v);
}

static void tvdb__nnvdb_sw_write_i32(tvdb__nnvdb_sw_t *sw, int32_t v) {
    tvdb__nnvdb_sw_write_u32(sw, (uint32_t)v);
}

static void tvdb__nnvdb_sw_write_i64(tvdb__nnvdb_sw_t *sw, int64_t v) {
    tvdb__nnvdb_sw_write_u64(sw, (uint64_t)v);
}

static void tvdb__nnvdb_sw_write_double(tvdb__nnvdb_sw_t *sw, double v) {
    union { double d; uint64_t u; } u;
    u.d = v;
    if (sw->swap_endian) u.u = tvdb__nnvdb_swap64(u.u);
    tvdb__nnvdb_sw_write(sw, 8, &u.u);
}

static void tvdb__nnvdb_sw_write_str(tvdb__nnvdb_sw_t *sw, const char *s,
                                     size_t len) {
    tvdb__nnvdb_sw_write(sw, len, s);
    if (len > 0 && s[len-1] != '\0') {
        tvdb__nnvdb_sw_write_u8(sw, 0);
    }
}

/* ========================================================================== */
/*  BLOSC decompression for NanoVDB                                            */
/* ========================================================================== */

static int tvdb__nnvdb_decompress_blosc(void *dst, size_t dst_size,
                                        const void *src, size_t src_size) {
    if (!dst || !src) return 0;

    int flags = 0;
    int typesize = 0;
    size_t nbytes = 0, cbytes = 0;
    if (LZ4_decompress_safe(src, dst, src_size, dst_size) < 0) return 0;

    const uint8_t *p = (const uint8_t *)src;
    flags = p[0];
    typesize = flags & 0x1F;
    nbytes = (size_t)p[1] | ((size_t)p[2] << 8) |
             ((size_t)p[3] << 16) | ((size_t)p[4] << 24);
    cbytes = (size_t)p[5] | ((size_t)p[6] << 8) |
             ((size_t)p[7] << 16) | ((size_t)p[8] << 24);

    if (nbytes > dst_size) return 0;
    (void)cbytes;

    int rc = LZ4_decompress_safe((const char *)src + 12, dst, src_size - 12,
                                  dst_size);
    return (rc >= 0) ? 1 : 0;
}

/* ========================================================================== */
/*  ZIP decompression for NanoVDB                                              */
/* ========================================================================== */

static int tvdb__nnvdb_decompress_zip(void *dst, size_t dst_size,
                                      const void *src, size_t src_size) {
    if (!dst || !src) return 0;

#if !defined(TVDB_USE_SYSTEM_ZLIB)
    mz_ulong decomp_size = (mz_ulong)dst_size;
    int rc = mz_uncompress((uint8_t *)dst, &decomp_size, src, src_size);
    return (rc == MZ_OK) ? 1 : 0;
#else
    uLongf decomp_size = (uLongf)dst_size;
    int rc = uncompress((uint8_t *)dst, &decomp_size, src, src_size);
    return (rc == Z_OK) ? 1 : 0;
#endif
}

/* ========================================================================== */
/*  Decompression wrapper                                                      */
/* ========================================================================== */

static int tvdb__nnvdb_decompress(void *dst, size_t dst_size,
                                  const void *src, size_t src_size,
                                  tvdb_nanovdb_codec_t codec) {
    switch (codec) {
        case TVDB_NANOVDB_CODEC_BLOSC:
            return tvdb__nnvdb_decompress_blosc(dst, dst_size, src, src_size);
        case TVDB_NANOVDB_CODEC_ZIP:
            return tvdb__nnvdb_decompress_zip(dst, dst_size, src, src_size);
        default:
            if (dst_size == src_size) {
                memcpy(dst, src, src_size);
                return 1;
            }
            return 0;
    }
}

/* ========================================================================== */
/*  File reading                                                              */
/* ========================================================================== */

static tvdb_status_t tvdb__nnvdb_read_header(tvdb__nnvdb_sr_t *sr,
                                              tvdb_nanovdb_file_header_t *hdr,
                                              tvdb_error_t *err) {
    hdr->magic = tvdb__nnvdb_sr_read_u64(sr);
    hdr->version = tvdb__nnvdb_sr_read_u32(sr);
    hdr->grid_count = tvdb__nnvdb_sr_read_u16(sr);
    hdr->codec = tvdb__nnvdb_sr_read_u16(sr);

    if (hdr->magic == 0) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_INVALID_HEADER,
                               "Empty or invalid NanoVDB file");
        return TVDB_ERROR_INVALID_HEADER;
    }

    if (hdr->magic == tvdb__nnvdb_swap64(TVDB_NANOVDB_MAGIC_FILE) ||
        hdr->magic == tvdb__nnvdb_swap64(TVDB_NANOVDB_MAGIC_NUMB)) {
        sr->swap_endian = 1;
        hdr->magic = tvdb__nnvdb_swap64(hdr->magic);
        hdr->version = tvdb__nnvdb_swap32(hdr->version);
        hdr->grid_count = tvdb__nnvdb_swap16(hdr->grid_count);
        hdr->codec = tvdb__nnvdb_swap16(hdr->codec);
    }

    if (hdr->magic != TVDB_NANOVDB_MAGIC_FILE &&
        hdr->magic != TVDB_NANOVDB_MAGIC_GRID &&
        hdr->magic != TVDB_NANOVDB_MAGIC_NUMB) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_INVALID_HEADER,
                               "Not a NanoVDB file");
        return TVDB_ERROR_INVALID_HEADER;
    }

    return TVDB_OK;
}

static tvdb_status_t tvdb__nnvdb_read_file_meta(tvdb__nnvdb_sr_t *sr,
                                                  tvdb_nanovdb_file_meta_t *meta,
                                                  tvdb_error_t *err) {
    meta->grid_size = tvdb__nnvdb_sr_read_u64(sr);
    meta->file_size = tvdb__nnvdb_sr_read_u64(sr);
    meta->name_key = tvdb__nnvdb_sr_read_u64(sr);
    meta->voxel_count = tvdb__nnvdb_sr_read_u64(sr);
    meta->grid_type = tvdb__nnvdb_sr_read_u32(sr);
    meta->grid_class = tvdb__nnvdb_sr_read_u32(sr);

    for (int i = 0; i < 3; i++)
        meta->world_bbox_min[i] = tvdb__nnvdb_sr_read_double(sr);
    for (int i = 0; i < 3; i++)
        meta->world_bbox_max[i] = tvdb__nnvdb_sr_read_double(sr);
    for (int i = 0; i < 3; i++)
        meta->index_bbox_min[i] = tvdb__nnvdb_sr_read_i32(sr);
    for (int i = 0; i < 3; i++)
        meta->index_bbox_max[i] = tvdb__nnvdb_sr_read_i32(sr);
    for (int i = 0; i < 3; i++)
        meta->voxel_size[i] = tvdb__nnvdb_sr_read_double(sr);

    meta->name_size = tvdb__nnvdb_sr_read_u32(sr);
    for (int i = 0; i < 4; i++)
        meta->node_count[i] = tvdb__nnvdb_sr_read_u32(sr);
    for (int i = 0; i < 3; i++)
        meta->tile_count[i] = tvdb__nnvdb_sr_read_u32(sr);
    meta->codec = tvdb__nnvdb_sr_read_u16(sr);
    meta->blind_data_count = tvdb__nnvdb_sr_read_u16(sr);
    meta->version = tvdb__nnvdb_sr_read_u32(sr);

    return TVDB_OK;
}

static tvdb_status_t tvdb__nnvdb_read_grid_data(tvdb__nnvdb_sr_t *sr,
                                                tvdb_nanovdb_grid_data_t *gd,
                                                tvdb_error_t *err) {
    gd->magic = tvdb__nnvdb_sr_read_u64(sr);
    gd->checksum = tvdb__nnvdb_sr_read_u64(sr);
    gd->version = tvdb__nnvdb_sr_read_u32(sr);
    gd->flags = tvdb__nnvdb_sr_read_u32(sr);
    gd->grid_index = tvdb__nnvdb_sr_read_u32(sr);
    gd->grid_count = tvdb__nnvdb_sr_read_u32(sr);
    gd->grid_size = tvdb__nnvdb_sr_read_u64(sr);
    tvdb__nnvdb_sr_read_str(sr, 256, gd->grid_name);

    for (int i = 0; i < 12; i++)
        gd->map[i] = tvdb__nnvdb_sr_read_double(sr);
    for (int i = 0; i < 3; i++)
        gd->world_bbox_min[i] = tvdb__nnvdb_sr_read_double(sr);
    for (int i = 0; i < 3; i++)
        gd->world_bbox_max[i] = tvdb__nnvdb_sr_read_double(sr);
    for (int i = 0; i < 3; i++)
        gd->voxel_size[i] = tvdb__nnvdb_sr_read_double(sr);

    gd->grid_class = tvdb__nnvdb_sr_read_u32(sr);
    gd->grid_type = tvdb__nnvdb_sr_read_u32(sr);
    gd->blind_metadata_offset = tvdb__nnvdb_sr_read_i64(sr);
    gd->blind_metadata_count = tvdb__nnvdb_sr_read_u32(sr);
    gd->data0 = tvdb__nnvdb_sr_read_u32(sr);
    gd->data1 = tvdb__nnvdb_sr_read_u64(sr);
    gd->data2 = tvdb__nnvdb_sr_read_u64(sr);

    return TVDB_OK;
}

static tvdb_status_t tvdb__nnvdb_read_tree_data(tvdb__nnvdb_sr_t *sr,
                                                 tvdb_nanovdb_tree_data_t *td,
                                                 tvdb_error_t *err) {
    for (int i = 0; i < 4; i++)
        td->node_offset[i] = tvdb__nnvdb_sr_read_i64(sr);
    for (int i = 0; i < 3; i++)
        td->node_count[i] = tvdb__nnvdb_sr_read_u32(sr);
    for (int i = 0; i < 3; i++)
        td->tile_count[i] = tvdb__nnvdb_sr_read_u32(sr);
    td->voxel_count = tvdb__nnvdb_sr_read_u64(sr);

    return TVDB_OK;
}

/* ========================================================================== */
/*  Public API implementation                                                  */
/* ========================================================================== */

tvdb_status_t tvdb_nanovdb_file_open(tvdb_nanovdb_file_t *file,
                                      const char *filepath_utf8,
                                      const tvdb_allocator_t *alloc,
                                      tvdb_error_t *err) {
    if (!file || !filepath_utf8) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                               "Invalid argument");
        return TVDB_ERROR_INVALID_ARGUMENT;
    }

    memset(file, 0, sizeof(*file));

    if (alloc) {
        file->alloc = *alloc;
    } else {
        file->alloc.malloc_fn = (void *(*)(size_t, void *))malloc;
        file->alloc.realloc_fn = (void *(*)(void *, size_t, size_t, void *))realloc;
        file->alloc.free_fn = (void (*)(void *, size_t, void *))free;
        file->alloc.user_ctx = NULL;
    }

#if !defined(TVDB_NO_MMAP)
    int fd = open(filepath_utf8, O_RDONLY);
    if (fd >= 0) {
        struct stat st;
        if (fstat(fd, &st) == 0) {
            file->file_size = (uint64_t)st.st_size;
            file->mmap_data = (const uint8_t *)mmap(NULL, st.st_size,
                                                      PROT_READ, MAP_PRIVATE,
                                                      fd, 0);
            if (file->mmap_data) {
                close(fd);
                return tvdb_nanovdb_file_open_memory(file, file->mmap_data,
                                                     file->file_size, alloc,
                                                     err);
            }
        }
        close(fd);
    }
#endif

    FILE *fp = fopen(filepath_utf8, "rb");
    if (!fp) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_IO,
                               "Failed to open file");
        return TVDB_ERROR_IO;
    }

    fseek(fp, 0, SEEK_END);
    long fsize = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    uint8_t *data = (uint8_t *)malloc((size_t)fsize);
    if (!data) {
        fclose(fp);
        tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
        return TVDB_ERROR_OUT_OF_MEMORY;
    }

    if (fread(data, 1, (size_t)fsize, fp) != (size_t)fsize) {
        free(data);
        fclose(fp);
        tvdb__nnvdb_set_error(err, TVDB_ERROR_IO, "Failed to read file");
        return TVDB_ERROR_IO;
    }
    fclose(fp);

    file->buffer = data;
    tvdb_status_t st = tvdb_nanovdb_file_open_memory(file, data, (size_t)fsize,
                                                      alloc, err);
    return st;
}

tvdb_status_t tvdb_nanovdb_file_open_memory(tvdb_nanovdb_file_t *file,
                                             const uint8_t *data,
                                             size_t data_len,
                                             const tvdb_allocator_t *alloc,
                                             tvdb_error_t *err) {
    if (!file || !data) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                               "Invalid argument");
        return TVDB_ERROR_INVALID_ARGUMENT;
    }

    memset(file, 0, sizeof(*file));
    file->file_size = data_len;

    if (alloc) {
        file->alloc = *alloc;
    } else {
        file->alloc.malloc_fn = (void *(*)(size_t, void *))malloc;
        file->alloc.realloc_fn = (void *(*)(void *, size_t, size_t, void *))realloc;
        file->alloc.free_fn = (void (*)(void *, size_t, void *))free;
        file->alloc.user_ctx = NULL;
    }

    tvdb__nnvdb_sr_t sr;
    tvdb__nnvdb_sr_init(&sr, data, data_len, 0);

    tvdb_nanovdb_file_header_t hdr;
    tvdb_status_t st = tvdb__nnvdb_read_header(&sr, &hdr, err);
    if (st != TVDB_OK) return st;

    file->version = hdr.version;
    file->grid_count = hdr.grid_count;
    file->codec = hdr.codec;

    if (hdr.magic == TVDB_NANOVDB_MAGIC_GRID) {
        file->num_grids = 1;
        file->grids = (tvdb_nanovdb_grid_t *)calloc(1,
                                     sizeof(tvdb_nanovdb_grid_t));
        if (!file->grids) {
            tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
            return TVDB_ERROR_OUT_OF_MEMORY;
        }
        file->grids[0].data = (uint8_t *)data;
        file->grids[0].size = data_len;
        file->grids[0].owns_data = 0;
        return TVDB_OK;
    }

    file->num_grids = hdr.grid_count;
    file->grids = (tvdb_nanovdb_grid_t *)calloc(file->num_grids,
                                     sizeof(tvdb_nanovdb_grid_t));
    if (!file->grids) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
        return TVDB_ERROR_OUT_OF_MEMORY;
    }

    for (uint16_t i = 0; i < hdr.grid_count; i++) {
        tvdb_nanovdb_file_meta_t meta;
        if (tvdb__nnvdb_read_file_meta(&sr, &meta, err) != TVDB_OK)
            return TVDB_ERROR_INVALID_DATA;

        file->grids[i].name = (char *)malloc(meta.name_size + 1);
        if (file->grids[i].name) {
            tvdb__nnvdb_sr_read(&sr, meta.name_size,
                               file->grids[i].name);
            file->grids[i].name[meta.name_size] = '\0';
        }

        file->grids[i].grid_type = meta.grid_type;
        file->grids[i].grid_class = meta.grid_class;
        file->grids[i].voxel_size[0] = meta.voxel_size[0];
        file->grids[i].voxel_size[1] = meta.voxel_size[1];
        file->grids[i].voxel_size[2] = meta.voxel_size[2];
        file->grids[i].world_bbox_min[0] = meta.world_bbox_min[0];
        file->grids[i].world_bbox_min[1] = meta.world_bbox_min[1];
        file->grids[i].world_bbox_min[2] = meta.world_bbox_min[2];
        file->grids[i].world_bbox_max[0] = meta.world_bbox_max[0];
        file->grids[i].world_bbox_max[1] = meta.world_bbox_max[1];
        file->grids[i].world_bbox_max[2] = meta.world_bbox_max[2];
        file->grids[i].index_bbox_min[0] = meta.index_bbox_min[0];
        file->grids[i].index_bbox_min[1] = meta.index_bbox_min[1];
        file->grids[i].index_bbox_min[2] = meta.index_bbox_min[2];
        file->grids[i].index_bbox_max[0] = meta.index_bbox_max[0];
        file->grids[i].index_bbox_max[1] = meta.index_bbox_max[1];
        file->grids[i].index_bbox_max[2] = meta.index_bbox_max[2];
        file->grids[i].active_voxel_count = meta.voxel_count;
        file->grids[i].node_count[0] = meta.node_count[0];
        file->grids[i].node_count[1] = meta.node_count[1];
        file->grids[i].node_count[2] = meta.node_count[2];
        file->grids[i].node_count[3] = meta.node_count[3];
        file->grids[i].tile_count[0] = meta.tile_count[0];
        file->grids[i].tile_count[1] = meta.tile_count[1];
        file->grids[i].tile_count[2] = meta.tile_count[2];
        file->grids[i].size = meta.grid_size;
    }

    for (uint16_t i = 0; i < hdr.grid_count; i++) {
        uint64_t grid_data_start = tvdb__nnvdb_sr_pos(&sr);
        uint64_t grid_size = file->grids[i].size;

        tvdb__nnvdb_sr_t gr;
        tvdb__nnvdb_sr_init(&gr, sr.data + grid_data_start,
                            sr.length - grid_data_start, sr.swap_endian);

        tvdb_nanovdb_grid_data_t gd;
        if (tvdb__nnvdb_read_grid_data(&gr, &gd, err) != TVDB_OK)
            return TVDB_ERROR_INVALID_DATA;

        tvdb_nanovdb_tree_data_t td;
        if (tvdb__nnvdb_read_tree_data(&gr, &td, err) != TVDB_OK)
            return TVDB_ERROR_INVALID_DATA;

        if (hdr.codec != TVDB_NANOVDB_CODEC_NONE && grid_size > 0) {
            uint64_t compressed_size = tvdb__nnvdb_sr_read_u64(&sr);

            uint8_t *decompressed = (uint8_t *)malloc((size_t)grid_size);
            if (!decompressed) {
                tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
                return TVDB_ERROR_OUT_OF_MEMORY;
            }

            if (compressed_size > 0 && compressed_size < (1ULL << 30)) {
                uint8_t *compressed = (uint8_t *)malloc((size_t)compressed_size);
                if (!compressed) {
                    free(decompressed);
                    tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
                    return TVDB_ERROR_OUT_OF_MEMORY;
                }

                tvdb__nnvdb_sr_read(&sr, (size_t)compressed_size, compressed);

                tvdb_nanovdb_codec_t codec = (hdr.codec == TVDB_NANOVDB_CODEC_BLOSC) ?
                                              TVDB_NANOVDB_CODEC_BLOSC : TVDB_NANOVDB_CODEC_ZIP;

                if (!tvdb__nnvdb_decompress(decompressed, (size_t)grid_size,
                                            compressed, (size_t)compressed_size, codec)) {
                    free(compressed);
                    free(decompressed);
                    tvdb__nnvdb_set_error(err, TVDB_ERROR_DECOMPRESSION_FAILED,
                                          "Failed to decompress grid data");
                    return TVDB_ERROR_DECOMPRESSION_FAILED;
                }
                free(compressed);
            } else {
                tvdb__nnvdb_sr_read(&sr, (size_t)grid_size, decompressed);
            }

            file->grids[i].data = decompressed;
            file->grids[i].size = grid_size;
            file->grids[i].owns_data = 1;
        } else {
            file->grids[i].data = (uint8_t *)(sr.data + grid_data_start);
            file->grids[i].owns_data = 0;
        }

        file->grids[i].tree_data_offset = 672;
        file->grids[i].leaf_data_offset = td.node_offset[0];
        file->grids[i].lower_data_offset = td.node_offset[1];
        file->grids[i].upper_data_offset = td.node_offset[2];
        file->grids[i].root_data_offset = td.node_offset[3];
    }

    return TVDB_OK;
}

void tvdb_nanovdb_file_close(tvdb_nanovdb_file_t *file) {
    if (!file) return;

    for (size_t i = 0; i < file->num_grids; i++) {
        if (file->grids[i].name)
            free(file->grids[i].name);
        if (file->grids[i].owns_data && file->grids[i].data)
            free(file->grids[i].data);
    }
    if (file->grids)
        free(file->grids);

    if (file->buffer)
        free(file->buffer);

#if !defined(TVDB_NO_MMAP)
    if (file->mmap_data)
        munmap((void *)file->mmap_data, file->file_size);
#endif

    memset(file, 0, sizeof(*file));
}

size_t tvdb_nanovdb_grid_count(const tvdb_nanovdb_file_t *file) {
    return file ? file->num_grids : 0;
}

const char *tvdb_nanovdb_grid_name(const tvdb_nanovdb_file_t *file,
                                   size_t idx) {
    if (!file || idx >= file->num_grids) return NULL;
    return file->grids[idx].name ? file->grids[idx].name : "";
}

uint32_t tvdb_nanovdb_grid_type(const tvdb_nanovdb_file_t *file,
                               size_t idx) {
    if (!file || idx >= file->num_grids) return 0;
    return file->grids[idx].grid_type;
}

uint32_t tvdb_nanovdb_grid_class(const tvdb_nanovdb_file_t *file,
                                 size_t idx) {
    if (!file || idx >= file->num_grids) return 0;
    return file->grids[idx].grid_class;
}

double tvdb_nanovdb_grid_voxel_size(const tvdb_nanovdb_file_t *file,
                                    size_t idx, int axis) {
    if (!file || idx >= file->num_grids || axis < 0 || axis > 2) return 0.0;
    return file->grids[idx].voxel_size[axis];
}

float tvdb_nanovdb_get_voxel_f(const tvdb_nanovdb_grid_t *grid,
                               int x, int y, int z) {
    if (!grid || grid->grid_type != TVDB_NANOVDB_GRID_TYPE_FLOAT) return 0.0f;

    int nx = grid->index_bbox_max[0] - grid->index_bbox_min[0] + 1;
    int ny = grid->index_bbox_max[1] - grid->index_bbox_min[1] + 1;

    if (x < grid->index_bbox_min[0] || x > grid->index_bbox_max[0] ||
        y < grid->index_bbox_min[1] || y > grid->index_bbox_max[1] ||
        z < grid->index_bbox_min[2] || z > grid->index_bbox_max[2]) {
        return 0.0f;
    }

    x -= grid->index_bbox_min[0];
    y -= grid->index_bbox_min[1];
    z -= grid->index_bbox_min[2];

    size_t idx = (size_t)(x + nx * (y + ny * z));
    const float *vals = (const float *)(grid->data + grid->leaf_data_offset + 64);
    return vals[idx];
}

double tvdb_nanovdb_get_voxel_d(const tvdb_nanovdb_grid_t *grid,
                               int x, int y, int z) {
    if (!grid || grid->grid_type != TVDB_NANOVDB_GRID_TYPE_DOUBLE) return 0.0;
    return 0.0;
}

int tvdb_nanovdb_is_voxel_active(const tvdb_nanovdb_grid_t *grid,
                                 int x, int y, int z) {
    if (!grid) return 0;
    if (x < grid->index_bbox_min[0] || x > grid->index_bbox_max[0] ||
        y < grid->index_bbox_min[1] || y > grid->index_bbox_max[1] ||
        z < grid->index_bbox_min[2] || z > grid->index_bbox_max[2]) {
        return 0;
    }
    return 1;
}

const char *tvdb_nanovdb_grid_type_name(uint32_t grid_type) {
    switch (grid_type) {
        case TVDB_NANOVDB_GRID_TYPE_FLOAT:    return "Float";
        case TVDB_NANOVDB_GRID_TYPE_DOUBLE:   return "Double";
        case TVDB_NANOVDB_GRID_TYPE_INT16:    return "Int16";
        case TVDB_NANOVDB_GRID_TYPE_INT32:    return "Int32";
        case TVDB_NANOVDB_GRID_TYPE_INT64:    return "Int64";
        case TVDB_NANOVDB_GRID_TYPE_VEC3F:    return "Vec3f";
        case TVDB_NANOVDB_GRID_TYPE_VEC3D:    return "Vec3d";
        case TVDB_NANOVDB_GRID_TYPE_MASK:      return "Mask";
        case TVDB_NANOVDB_GRID_TYPE_HALF:     return "Half";
        case TVDB_NANOVDB_GRID_TYPE_UINT32:   return "UInt32";
        case TVDB_NANOVDB_GRID_TYPE_BOOLEAN:  return "Boolean";
        case TVDB_NANOVDB_GRID_TYPE_RGBA8:    return "RGBA8";
        case TVDB_NANOVDB_GRID_TYPE_FP4:      return "Fp4";
        case TVDB_NANOVDB_GRID_TYPE_FP8:      return "Fp8";
        case TVDB_NANOVDB_GRID_TYPE_FP16:     return "Fp16";
        case TVDB_NANOVDB_GRID_TYPE_FPN:      return "FpN";
        case TVDB_NANOVDB_GRID_TYPE_VEC4F:    return "Vec4f";
        case TVDB_NANOVDB_GRID_TYPE_VEC4D:    return "Vec4d";
        case TVDB_NANOVDB_GRID_TYPE_INDEX:    return "Index";
        case TVDB_NANOVDB_GRID_TYPE_POINT_INDEX: return "PointIndex";
        default:                              return "Unknown";
    }
}

const char *tvdb_nanovdb_grid_class_name(uint32_t grid_class) {
    switch (grid_class) {
        case TVDB_NANOVDB_GRID_CLASS_LEVEL_SET:   return "LevelSet";
        case TVDB_NANOVDB_GRID_CLASS_FOG_VOLUME:  return "FogVolume";
        case TVDB_NANOVDB_GRID_CLASS_STAGGERED:   return "Staggered";
        case TVDB_NANOVDB_GRID_CLASS_COLLISION:    return "Collision";
        case TVDB_NANOVDB_GRID_CLASS_POINT_INDEX:  return "PointIndex";
        case TVDB_NANOVDB_GRID_CLASS_POINT_DATA:   return "PointData";
        default:                                   return "Unknown";
    }
}

int tvdb_nanovdb_is_big_endian_file(const tvdb_nanovdb_file_t *file) {
    (void)file;
    return !tvdb__nnvdb_is_little_endian();
}

/* ========================================================================== */
/*  BLOSC compression for NanoVDB write                                        */
/* ========================================================================== */

static int tvdb__nnvdb_compress_blosc(void **dst, size_t *dst_size,
                                       const void *src, size_t src_size) {
    if (!src || !dst) return 0;

    size_t max_size = (size_t)LZ4_compressBound((int)src_size) + 12;
    *dst = malloc(max_size);
    if (!*dst) return 0;

    uint8_t *out = (uint8_t *)*dst;

    out[0] = 0;
    out[1] = (src_size & 0xFF);
    out[2] = (src_size >> 8) & 0xFF;
    out[3] = (src_size >> 16) & 0xFF;
    out[4] = (src_size >> 24) & 0xFF;

    int compressed = LZ4_compress_default((const char *)src,
                                           (char *)out + 12,
                                           (int)src_size,
                                           (int)(max_size - 12));
    if (compressed <= 0) {
        free(*dst);
        *dst = NULL;
        return 0;
    }

    *dst_size = (size_t)compressed + 12;
    return 1;
}

/* ========================================================================== */
/*  ZIP compression for NanoVDB write                                           */
/* ========================================================================== */

static int tvdb__nnvdb_compress_zip(void **dst, size_t *dst_size,
                                     const void *src, size_t src_size) {
    if (!src || !dst) return 0;

#if !defined(TVDB_USE_SYSTEM_ZLIB)
    mz_ulong dest_size = mz_compressBound((mz_ulong)src_size);
    *dst = malloc(dest_size);
    if (!*dst) return 0;

    int rc = mz_compress((uint8_t *)*dst, &dest_size, src, src_size);
    if (rc != MZ_OK) {
        free(*dst);
        *dst = NULL;
        return 0;
    }
    *dst_size = (size_t)dest_size;
    return 1;
#else
    uLongf dest_size = compressBound((uLongf)src_size);
    *dst = malloc(dest_size);
    if (!*dst) return 0;

    int rc = compress((uint8_t *)*dst, &dest_size, src, src_size);
    if (rc != Z_OK) {
        free(*dst);
        *dst = NULL;
        return 0;
    }
    *dst_size = (size_t)dest_size;
    return 1;
#endif
}

/* ========================================================================== */
/*  Internal write helpers                                                     */
/* ========================================================================== */

/* Grid data constants */
#define TVDB_NANOVDB_GRID_DATA_SIZE 672
#define TVDB_NANOVDB_TREE_DATA_SIZE 64
#define TVDB_NANOVDB_ROOT_DATA_ALIGN 32
#define TVDB_NANOVDB_LEAF_NODE_ALIGN 32

static void tvdb__nnvdb_write_file_header(tvdb__nnvdb_sw_t *sw,
                                          const tvdb_nanovdb_file_t *file) {
    tvdb__nnvdb_sw_write_u64(sw, TVDB_NANOVDB_MAGIC_FILE);
    uint32_t version = (TVDB_NANOVDB_VERSION_MAJOR << 24) |
                       (TVDB_NANOVDB_VERSION_MINOR << 16) |
                       TVDB_NANOVDB_VERSION_PATCH;
    tvdb__nnvdb_sw_write_u32(sw, version);
    tvdb__nnvdb_sw_write_u16(sw, (uint16_t)file->grid_count);
    tvdb__nnvdb_sw_write_u16(sw, (uint16_t)file->codec);
}

static void tvdb__nnvdb_write_file_meta(tvdb__nnvdb_sw_t *sw,
                                        const tvdb_nanovdb_grid_t *grid) {
    tvdb__nnvdb_sw_write_u64(sw, grid->size);
    tvdb__nnvdb_sw_write_u64(sw, grid->size);
    tvdb__nnvdb_sw_write_u64(sw, 0);
    tvdb__nnvdb_sw_write_u64(sw, grid->active_voxel_count);
    tvdb__nnvdb_sw_write_u32(sw, grid->grid_type);
    tvdb__nnvdb_sw_write_u32(sw, grid->grid_class);

    for (int i = 0; i < 3; i++)
        tvdb__nnvdb_sw_write_double(sw, grid->world_bbox_min[i]);
    for (int i = 0; i < 3; i++)
        tvdb__nnvdb_sw_write_double(sw, grid->world_bbox_max[i]);
    for (int i = 0; i < 3; i++)
        tvdb__nnvdb_sw_write_i32(sw, grid->index_bbox_min[i]);
    for (int i = 0; i < 3; i++)
        tvdb__nnvdb_sw_write_i32(sw, grid->index_bbox_max[i]);
    for (int i = 0; i < 3; i++)
        tvdb__nnvdb_sw_write_double(sw, grid->voxel_size[i]);

    size_t name_len = grid->name ? strlen(grid->name) : 0;
    tvdb__nnvdb_sw_write_u32(sw, (uint32_t)name_len);

    for (int i = 0; i < 4; i++)
        tvdb__nnvdb_sw_write_u32(sw, grid->node_count[i]);
    for (int i = 0; i < 3; i++)
        tvdb__nnvdb_sw_write_u32(sw, grid->tile_count[i]);

    tvdb__nnvdb_sw_write_u16(sw, 0);
    tvdb__nnvdb_sw_write_u16(sw, 0);

    uint32_t version = (TVDB_NANOVDB_VERSION_MAJOR << 24) |
                       (TVDB_NANOVDB_VERSION_MINOR << 16) |
                       TVDB_NANOVDB_VERSION_PATCH;
    tvdb__nnvdb_sw_write_u32(sw, version);
}

static void tvdb__nnvdb_write_grid_name(tvdb__nnvdb_sw_t *sw,
                                        const char *name) {
    size_t len = name ? strlen(name) : 0;
    if (len > 0) {
        tvdb__nnvdb_sw_write(sw, len, name);
    }
    tvdb__nnvdb_sw_write_u8(sw, 0);
}

static int tvdb__nnvdb_align(tvdb__nnvdb_sw_t *sw, size_t alignment) {
    size_t pos = sw->pos;
    size_t mod = pos % alignment;
    if (mod > 0) {
        size_t pad = alignment - mod;
        if (sw->pos + pad > sw->capacity) return 0;
        for (size_t i = 0; i < pad; i++) {
            sw->data[sw->pos++] = 0;
        }
    }
    return 1;
}

/* ========================================================================== */
/*  Write implementations                                                      */
/* ========================================================================== */

tvdb_status_t tvdb_nanovdb_write_to_memory(const tvdb_nanovdb_file_t *file,
                                            uint32_t compression_flags,
                                            uint8_t **out_data,
                                            size_t *out_size,
                                            tvdb_error_t *err) {
    if (!file || !out_data || !out_size) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                               "Invalid argument");
        return TVDB_ERROR_INVALID_ARGUMENT;
    }

    *out_data = NULL;
    *out_size = 0;

    if (file->num_grids == 0) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_INVALID_DATA,
                               "No grids to write");
        return TVDB_ERROR_INVALID_DATA;
    }

    tvdb_nanovdb_codec_t codec = TVDB_NANOVDB_CODEC_NONE;
    if (compression_flags & TVDB_NANOVDB_CODEC_BLOSC) {
        codec = TVDB_NANOVDB_CODEC_BLOSC;
    } else if (compression_flags & TVDB_NANOVDB_CODEC_ZIP) {
        codec = TVDB_NANOVDB_CODEC_ZIP;
    }

    size_t initial_capacity = 1024 * 1024;
    uint8_t *buffer = (uint8_t *)malloc(initial_capacity);
    if (!buffer) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
        return TVDB_ERROR_OUT_OF_MEMORY;
    }

    tvdb__nnvdb_sw_t sw;
    tvdb__nnvdb_sw_init(&sw, buffer, initial_capacity);

    tvdb_nanovdb_file_t wf;
    memset(&wf, 0, sizeof(wf));
    wf.version = (TVDB_NANOVDB_VERSION_MAJOR << 24) |
                 (TVDB_NANOVDB_VERSION_MINOR << 16) |
                 TVDB_NANOVDB_VERSION_PATCH;
    wf.grid_count = (uint16_t)file->num_grids;
    wf.codec = codec;

    tvdb__nnvdb_write_file_header(&sw, &wf);

    for (size_t i = 0; i < file->num_grids; i++) {
        tvdb__nnvdb_write_file_meta(&sw, &file->grids[i]);
        tvdb__nnvdb_write_grid_name(&sw, file->grids[i].name);
    }

    for (size_t i = 0; i < file->num_grids; i++) {
        const tvdb_nanovdb_grid_t *grid = &file->grids[i];

        if (!grid->data || grid->size == 0) {
            continue;
        }

        if (codec != TVDB_NANOVDB_CODEC_NONE) {
            void *compressed = NULL;
            size_t compressed_size = 0;

            int ok = 0;
            if (codec == TVDB_NANOVDB_CODEC_BLOSC) {
                ok = tvdb__nnvdb_compress_blosc(&compressed, &compressed_size,
                                                 grid->data, grid->size);
            } else if (codec == TVDB_NANOVDB_CODEC_ZIP) {
                ok = tvdb__nnvdb_compress_zip(&compressed, &compressed_size,
                                               grid->data, grid->size);
            }

            if (ok && compressed && compressed_size < grid->size) {
                tvdb__nnvdb_sw_write_u64(&sw, compressed_size);
                if (sw.pos + compressed_size > sw.capacity) {
                    size_t new_cap = sw.capacity * 2 + compressed_size;
                    uint8_t *new_buf = (uint8_t *)realloc(sw.data, new_cap);
                    if (!new_buf) {
                        free(compressed);
                        free(buffer);
                        tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
                        return TVDB_ERROR_OUT_OF_MEMORY;
                    }
                    sw.data = new_buf;
                    sw.capacity = new_cap;
                }
                memcpy(sw.data + sw.pos, compressed, compressed_size);
                sw.pos += compressed_size;
                free(compressed);
            } else {
                if (compressed) free(compressed);
                if (sw.pos + grid->size > sw.capacity) {
                    size_t new_cap = sw.capacity * 2 + grid->size;
                    uint8_t *new_buf = (uint8_t *)realloc(sw.data, new_cap);
                    if (!new_buf) {
                        free(buffer);
                        tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
                        return TVDB_ERROR_OUT_OF_MEMORY;
                    }
                    sw.data = new_buf;
                    sw.capacity = new_cap;
                }
                memcpy(sw.data + sw.pos, grid->data, grid->size);
                sw.pos += grid->size;
            }
        } else {
            if (sw.pos + grid->size > sw.capacity) {
                size_t new_cap = sw.capacity * 2 + grid->size;
                uint8_t *new_buf = (uint8_t *)realloc(sw.data, new_cap);
                if (!new_buf) {
                    free(buffer);
                    tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
                    return TVDB_ERROR_OUT_OF_MEMORY;
                }
                sw.data = new_buf;
                sw.capacity = new_cap;
            }
            memcpy(sw.data + sw.pos, grid->data, grid->size);
            sw.pos += grid->size;
        }
    }

    *out_data = sw.data;
    *out_size = sw.pos;
    return TVDB_OK;
}

tvdb_status_t tvdb_nanovdb_file_save(const tvdb_nanovdb_file_t *file,
                                      const char *filepath_utf8,
                                      uint32_t compression_flags,
                                      int use_mmap,
                                      tvdb_error_t *err) {
    (void)use_mmap;

    uint8_t *data = NULL;
    size_t data_size = 0;

    tvdb_status_t st = tvdb_nanovdb_write_to_memory(file, compression_flags,
                                                     &data, &data_size, err);
    if (st != TVDB_OK) return st;

#if defined(_WIN32)
    FILE *fp = fopen(filepath_utf8, "wb");
#else
    FILE *fp = fopen(filepath_utf8, "wb");
#endif
    if (!fp) {
        free(data);
        tvdb__nnvdb_set_error(err, TVDB_ERROR_IO, "Failed to open file");
        return TVDB_ERROR_IO;
    }

    if (fwrite(data, 1, data_size, fp) != data_size) {
        fclose(fp);
        free(data);
        tvdb__nnvdb_set_error(err, TVDB_ERROR_IO, "Failed to write file");
        return TVDB_ERROR_IO;
    }

    fclose(fp);
    free(data);
    return TVDB_OK;
}

/* ========================================================================== */
/*  Node size calculations                                                     */
/* ========================================================================== */

uint32_t tvdb_nanovdb_value_size(uint32_t grid_type) {
    switch (grid_type) {
        case TVDB_NANOVDB_GRID_TYPE_FLOAT:
        case TVDB_NANOVDB_GRID_TYPE_UINT32:
        case TVDB_NANOVDB_GRID_TYPE_INT32:
            return 4;
        case TVDB_NANOVDB_GRID_TYPE_DOUBLE:
        case TVDB_NANOVDB_GRID_TYPE_INT64:
            return 8;
        case TVDB_NANOVDB_GRID_TYPE_INT16:
        case TVDB_NANOVDB_GRID_TYPE_HALF:
            return 2;
        case TVDB_NANOVDB_GRID_TYPE_VEC3F:
            return 12;
        case TVDB_NANOVDB_GRID_TYPE_VEC3D:
            return 24;
        case TVDB_NANOVDB_GRID_TYPE_BOOLEAN:
        case TVDB_NANOVDB_GRID_TYPE_MASK:
            return 1;
        case TVDB_NANOVDB_GRID_TYPE_RGBA8:
            return 4;
        case TVDB_NANOVDB_GRID_TYPE_VEC4F:
            return 16;
        case TVDB_NANOVDB_GRID_TYPE_VEC4D:
            return 32;
        case TVDB_NANOVDB_GRID_TYPE_UINT8:
            return 1;
        default:
            return 4;
    }
}

uint64_t tvdb_nanovdb_leaf_node_size(uint32_t grid_type) {
    uint32_t value_size = tvdb_nanovdb_value_size(grid_type);
    uint32_t value_bytes = (value_size <= 4) ? 4 : 8;
    return 32 + 64 + 16 + (uint64_t)(512 * value_bytes);
}

uint64_t tvdb_nanovdb_lower_node_size(uint32_t grid_type) {
    uint32_t value_size = tvdb_nanovdb_value_size(grid_type);
    uint32_t value_bytes = (value_size <= 4) ? 4 : 8;
    return 32 + 1024 + 1024 + 16 + (uint64_t)(4096 * value_bytes);
}

uint64_t tvdb_nanovdb_upper_node_size(uint32_t grid_type) {
    uint32_t value_size = tvdb_nanovdb_value_size(grid_type);
    uint32_t value_bytes = (value_size <= 4) ? 4 : 8;
    return 32 + 8192 + 8192 + 16 + (uint64_t)(32768 * value_bytes);
}

uint64_t tvdb_nanovdb_root_tile_size(void) {
    return 32;
}

/* ========================================================================== */
/*  Grid creation and destruction                                             */
/* ========================================================================== */

tvdb_status_t tvdb_nanovdb_create_grid(tvdb_nanovdb_grid_t *grid,
                                       const char *name,
                                       uint32_t grid_type,
                                       uint32_t grid_class,
                                       int32_t min_coord[3],
                                       int32_t max_coord[3],
                                       const tvdb_allocator_t *alloc,
                                       tvdb_error_t *err) {
    if (!grid || !name) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "Invalid argument");
        return TVDB_ERROR_INVALID_ARGUMENT;
    }

    memset(grid, 0, sizeof(*grid));

    grid->name = (char *)malloc(strlen(name) + 1);
    if (!grid->name) {
        tvdb__nnvdb_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
        return TVDB_ERROR_OUT_OF_MEMORY;
    }
    strcpy(grid->name, name);

    grid->grid_type = grid_type;
    grid->grid_class = grid_class;

    for (int i = 0; i < 3; i++) {
        grid->voxel_size[i] = 1.0;
        grid->index_bbox_min[i] = min_coord[i];
        grid->index_bbox_max[i] = max_coord[i];
        grid->world_bbox_min[i] = (double)min_coord[i];
        grid->world_bbox_max[i] = (double)max_coord[i];
    }

    grid->node_count[0] = 0;
    grid->node_count[1] = 0;
    grid->node_count[2] = 0;
    grid->node_count[3] = 1;
    grid->tile_count[0] = 0;
    grid->tile_count[1] = 0;
    grid->tile_count[2] = 0;
    grid->active_voxel_count = 0;
    grid->owns_data = 1;

    grid->data = NULL;
    grid->size = 0;

    return TVDB_OK;
}

void tvdb_nanovdb_destroy_grid(tvdb_nanovdb_grid_t *grid,
                               const tvdb_allocator_t *alloc) {
    (void)alloc;
    if (!grid) return;
    if (grid->name) free(grid->name);
    if (grid->owns_data && grid->data) free(grid->data);
    memset(grid, 0, sizeof(*grid));
}

#endif /* TINYVDB_NANOVDB_IMPLEMENTATION */

#endif /* TINYVDB_NANOVDB_H_ */
