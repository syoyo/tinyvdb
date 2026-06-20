#include "tinyvdb_mesh.h"
#include "tvdb_memory.h"
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <assert.h>
#include <stdint.h>

#define TVDB_MAX_GRID_DIM 2048

static const int MC_EDGE_TABLE[256] = {
  0x0  , 0x109, 0x203, 0x30a, 0x406, 0x50f, 0x605, 0x70c,
  0x80c, 0x905, 0xa0f, 0xb06, 0xc0a, 0xd03, 0xe09, 0xf00,
  0x190, 0x99 , 0x393, 0x29a, 0x596, 0x49f, 0x795, 0x69c,
  0x99c, 0x895, 0xb9f, 0xa96, 0xd9a, 0xc93, 0xf99, 0xe90,
  0x230, 0x339, 0x33 , 0x13a, 0x636, 0x73f, 0x435, 0x53c,
  0xa3c, 0xb35, 0x83f, 0x936, 0xe3a, 0xf33, 0xc39, 0xd30,
  0x3a0, 0x2a9, 0x1a3, 0xaa , 0x7a6, 0x6af, 0x5a5, 0x4ac,
  0xbac, 0xaa5, 0x9af, 0x8a6, 0xfaa, 0xea3, 0xda9, 0xca0,
  0x460, 0x569, 0x663, 0x76a, 0x66 , 0x16f, 0x265, 0x36c,
  0xc6c, 0xd65, 0xe6f, 0xf66, 0x86a, 0x963, 0xa69, 0xb60,
  0x5f0, 0x4f9, 0x7f3, 0x6fa, 0x1f6, 0xff , 0x3f5, 0x2fc,
  0xdfc, 0xcf5, 0xfff, 0xef6, 0x9fa, 0x8f3, 0xbf9, 0xaf0,
  0x650, 0x759, 0x453, 0x55a, 0x256, 0x35f, 0x55 , 0x15c,
  0xe5c, 0xf55, 0xc5f, 0xd56, 0xa5a, 0xb53, 0x859, 0x950,
  0x7c0, 0x6c9, 0x5c3, 0x4ca, 0x3c6, 0x2cf, 0x1c5, 0xcc ,
  0xfcc, 0xec5, 0xdcf, 0xcc6, 0xbca, 0xac3, 0x9c9, 0x8c0,
  0x8c0, 0x9c9, 0xac3, 0xbca, 0xcc6, 0xdcf, 0xec5, 0xfcc,
  0xcc , 0x1c5, 0x2cf, 0x3c6, 0x4ca, 0x5c3, 0x6c9, 0x7c0,
  0x950, 0x859, 0xb53, 0xa5a, 0xd56, 0xc5f, 0xf55, 0xe5c,
  0x15c, 0x55 , 0x35f, 0x256, 0x55a, 0x453, 0x759, 0x650,
  0xaf0, 0xbf9, 0x8f3, 0x9fa, 0xef6, 0xfff, 0xcf5, 0xdfc,
  0x2fc, 0x3f5, 0xff , 0x1f6, 0x6fa, 0x7f3, 0x4f9, 0x5f0,
  0xb60, 0xa69, 0x963, 0x86a, 0xf66, 0xe6f, 0xd65, 0xc6c,
  0x36c, 0x265, 0x16f, 0x66 , 0x76a, 0x663, 0x569, 0x460,
  0xca0, 0xda9, 0xea3, 0xfaa, 0x8a6, 0x9af, 0xaa5, 0xbac,
  0x4ac, 0x5a5, 0x6af, 0x7a6, 0xaa , 0x1a3, 0x2a9, 0x3a0,
  0xd30, 0xc39, 0xf33, 0xe3a, 0x936, 0x83f, 0xb35, 0xa3c,
  0x53c, 0x435, 0x73f, 0x636, 0x13a, 0x33 , 0x339, 0x230,
  0xe90, 0xf99, 0xc93, 0xd9a, 0xa96, 0xb9f, 0x895, 0x99c,
  0x69c, 0x795, 0x49f, 0x596, 0x29a, 0x393, 0x99 , 0x190,
  0xf00, 0xe09, 0xd03, 0xc0a, 0xb06, 0xa0f, 0x905, 0x80c,
  0x70c, 0x605, 0x50f, 0x406, 0x30a, 0x203, 0x109, 0x0
};

static const int MC_TRI_TABLE[256][16] = {
  {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,8,3,9,8,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,2,10,0,2,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,8,3,2,10,8,10,9,8,-1,-1,-1,-1,-1,-1,-1},
  {3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,11,2,8,11,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,11,2,1,9,11,9,8,11,-1,-1,-1,-1,-1,-1,-1},
  {3,10,1,11,10,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,10,1,0,8,10,8,11,10,-1,-1,-1,-1,-1,-1,-1},
  {3,9,0,3,11,9,11,10,9,-1,-1,-1,-1,-1,-1,-1},
  {9,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,7,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,3,0,7,3,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,1,9,4,7,1,7,3,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,4,7,3,0,4,1,2,10,-1,-1,-1,-1,-1,-1,-1},
  {9,2,10,9,0,2,8,4,7,-1,-1,-1,-1,-1,-1,-1},
  {2,10,9,2,9,7,2,7,3,7,9,4,-1,-1,-1,-1},
  {8,4,7,3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {11,4,7,11,2,4,2,0,4,-1,-1,-1,-1,-1,-1,-1},
  {9,0,1,8,4,7,2,3,11,-1,-1,-1,-1,-1,-1,-1},
  {4,7,11,9,4,11,9,11,2,9,2,1,-1,-1,-1,-1},
  {3,10,1,3,11,10,7,8,4,-1,-1,-1,-1,-1,-1,-1},
  {1,11,10,1,4,11,1,0,4,7,11,4,-1,-1,-1,-1},
  {4,7,8,9,0,11,9,11,10,11,0,3,-1,-1,-1,-1},
  {4,7,11,4,11,9,9,11,10,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,5,4,1,5,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,5,4,8,3,5,3,1,5,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,1,2,10,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {5,2,10,5,4,2,4,0,2,-1,-1,-1,-1,-1,-1,-1},
  {2,10,5,3,2,5,3,5,4,3,4,8,-1,-1,-1,-1},
  {9,5,4,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,11,2,0,8,11,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {0,5,4,0,1,5,2,3,11,-1,-1,-1,-1,-1,-1,-1},
  {2,1,5,2,5,8,2,8,11,4,8,5,-1,-1,-1,-1},
  {10,3,11,10,1,3,9,5,4,-1,-1,-1,-1,-1,-1,-1},
  {4,9,5,0,8,1,8,10,1,8,11,10,-1,-1,-1,-1},
  {5,4,0,5,0,11,5,11,10,11,0,3,-1,-1,-1,-1},
  {5,4,8,5,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1},
  {9,7,8,5,7,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,3,0,9,5,3,5,7,3,-1,-1,-1,-1,-1,-1,-1},
  {0,7,8,0,1,7,1,5,7,-1,-1,-1,-1,-1,-1,-1},
  {1,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,7,8,9,5,7,10,1,2,-1,-1,-1,-1,-1,-1,-1},
  {10,1,2,9,5,0,5,3,0,5,7,3,-1,-1,-1,-1},
  {8,0,2,8,2,5,8,5,7,10,5,2,-1,-1,-1,-1},
  {2,10,5,2,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1},
  {7,9,5,7,8,9,3,11,2,-1,-1,-1,-1,-1,-1,-1},
  {9,5,7,9,7,2,9,2,0,2,7,11,-1,-1,-1,-1},
  {2,3,11,0,1,8,1,7,8,1,5,7,-1,-1,-1,-1},
  {11,2,1,11,1,7,7,1,5,-1,-1,-1,-1,-1,-1,-1},
  {9,5,8,8,5,7,10,1,3,10,3,11,-1,-1,-1,-1},
  {5,1,11,5,11,6,1,0,11,7,11,4,0,4,11,-1},
  {0,5,9,0,6,5,0,3,6,11,6,3,8,4,7,-1},
  {6,5,9,6,9,11,4,7,9,7,11,9,-1,-1,-1,-1},
  {10,4,9,6,4,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,10,6,4,9,10,0,8,3,-1,-1,-1,-1,-1,-1,-1},
  {10,0,1,10,6,0,6,4,0,-1,-1,-1,-1,-1,-1,-1},
  {8,3,1,8,1,6,8,6,4,6,1,10,-1,-1,-1,-1},
  {1,4,9,1,2,4,2,6,4,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,1,2,10,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {0,2,4,4,2,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,3,2,8,2,4,4,2,6,-1,-1,-1,-1,-1,-1,-1},
  {10,4,9,10,6,4,11,2,3,-1,-1,-1,-1,-1,-1,-1},
  {0,8,2,2,8,11,4,9,10,4,10,6,-1,-1,-1,-1},
  {3,11,2,0,1,6,0,6,4,6,1,10,-1,-1,-1,-1},
  {6,4,1,6,1,10,4,8,1,2,1,11,8,11,1,-1},
  {9,6,4,9,3,6,9,1,3,11,6,3,-1,-1,-1,-1},
  {8,11,1,8,1,0,11,6,1,9,1,4,6,4,1,-1},
  {3,11,6,3,6,0,0,6,4,-1,-1,-1,-1,-1,-1,-1},
  {6,4,8,11,6,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,10,6,7,8,10,8,9,10,-1,-1,-1,-1,-1,-1,-1},
  {0,7,3,0,10,7,0,9,10,6,7,10,-1,-1,-1,-1},
  {1,10,7,1,7,8,1,8,0,-1,-1,-1,-1,-1,-1,-1},
  {10,7,6,1,7,10,1,8,7,1,0,8,-1,-1,-1,-1},
  {1,2,6,1,6,8,1,8,9,8,6,7,-1,-1,-1,-1},
  {2,6,9,2,9,1,6,7,9,0,9,3,7,3,9,-1},
  {7,8,0,7,0,6,6,0,2,-1,-1,-1,-1,-1,-1,-1},
  {7,3,2,6,7,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,11,10,6,8,10,8,9,8,6,7,-1,-1,-1,-1},
  {2,0,7,2,7,11,0,9,7,6,7,10,9,10,7,-1},
  {1,8,0,1,7,8,1,10,7,6,7,10,2,3,11,-1},
  {11,2,1,11,1,7,10,6,1,6,7,1,-1,-1,-1,-1},
  {8,9,6,8,6,7,9,1,6,11,6,3,1,3,6,-1},
  {0,9,1,11,6,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,8,0,7,0,6,3,11,0,11,6,0,-1,-1,-1,-1},
  {7,11,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,11,7,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,11,7,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,1,9,8,3,1,11,7,6,-1,-1,-1,-1,-1,-1,-1},
  {10,1,2,6,11,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,3,0,8,6,11,7,-1,-1,-1,-1,-1,-1,-1},
  {2,9,0,2,10,9,6,11,7,-1,-1,-1,-1,-1,-1,-1},
  {6,11,7,2,10,3,10,8,3,10,9,8,-1,-1,-1,-1},
  {7,2,3,6,2,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,0,8,7,6,0,6,2,0,-1,-1,-1,-1,-1,-1,-1},
  {2,7,6,2,3,7,0,1,9,-1,-1,-1,-1,-1,-1,-1},
  {1,6,2,1,8,6,1,9,8,8,7,6,-1,-1,-1,-1},
  {10,7,6,10,1,7,1,3,7,-1,-1,-1,-1,-1,-1,-1},
  {10,7,6,1,7,10,1,8,7,1,0,8,-1,-1,-1,-1},
  {0,3,7,0,7,10,0,10,9,6,10,7,-1,-1,-1,-1},
  {7,6,10,7,10,8,8,10,9,-1,-1,-1,-1,-1,-1,-1},
  {6,8,4,11,8,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,6,11,3,0,6,0,4,6,-1,-1,-1,-1,-1,-1,-1},
  {8,6,11,8,4,6,9,0,1,-1,-1,-1,-1,-1,-1,-1},
  {9,4,6,9,6,3,9,3,1,11,3,6,-1,-1,-1,-1},
  {6,8,4,6,11,8,2,10,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,3,0,11,0,6,11,0,4,6,-1,-1,-1,-1},
  {4,11,8,4,6,11,0,2,9,2,10,9,-1,-1,-1,-1},
  {10,9,3,10,3,2,9,4,3,11,3,6,4,6,3,-1},
  {8,2,3,8,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1},
  {0,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,2,3,4,2,4,6,4,3,8,-1,-1,-1,-1},
  {1,9,4,1,4,2,2,4,6,-1,-1,-1,-1,-1,-1,-1},
  {8,1,3,8,6,1,8,4,6,6,10,1,-1,-1,-1,-1},
  {10,1,0,10,0,6,6,0,4,-1,-1,-1,-1,-1,-1,-1},
  {4,6,3,4,3,8,6,10,3,0,3,9,10,9,3,-1},
  {10,9,4,6,10,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,9,5,7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,4,9,5,11,7,6,-1,-1,-1,-1,-1,-1,-1},
  {1,10,11,1,11,4,1,4,0,7,4,11,-1,-1,-1,-1},
  {3,1,4,3,4,8,1,10,4,7,4,11,10,11,4,-1},
  {4,11,7,9,11,4,9,2,11,9,1,2,-1,-1,-1,-1},
  {9,7,4,9,11,7,9,1,11,2,11,1,0,8,3,-1},
  {11,7,4,11,4,2,2,4,0,-1,-1,-1,-1,-1,-1,-1},
  {11,7,4,11,4,2,8,3,4,3,2,4,-1,-1,-1,-1},
  {2,9,10,2,7,9,2,3,7,7,4,9,-1,-1,-1,-1},
  {9,10,7,9,7,4,10,2,7,8,7,0,2,0,7,-1},
  {3,7,10,3,10,2,7,4,10,1,10,0,4,0,10,-1},
  {1,10,2,8,7,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,9,1,4,1,7,7,1,3,-1,-1,-1,-1,-1,-1,-1},
  {4,9,1,4,1,7,0,8,1,8,7,1,-1,-1,-1,-1},
  {4,0,3,7,4,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,8,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,10,8,10,11,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,9,3,9,11,11,9,10,-1,-1,-1,-1,-1,-1,-1},
  {0,1,10,0,10,8,8,10,11,-1,-1,-1,-1,-1,-1,-1},
  {3,1,10,11,3,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,11,1,11,9,9,11,8,-1,-1,-1,-1,-1,-1,-1},
  {3,0,9,3,9,11,1,2,9,2,11,9,-1,-1,-1,-1},
  {0,2,11,8,0,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,2,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,8,2,8,10,10,8,9,-1,-1,-1,-1,-1,-1,-1},
  {9,10,2,0,9,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,8,2,8,10,0,1,8,1,10,8,-1,-1,-1,-1},
  {1,10,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,3,8,9,1,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,9,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,3,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1}
};

static void* arena_alloc_wrapper(tvdb_arena_allocator_t* arena, size_t size) {
    if (!arena) return malloc(size);
    return tvdb_arena_alloc(arena, size);
}

// C-compatible math helpers
static inline float dot_c(tvdb_vec3f a, tvdb_vec3f b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
static inline tvdb_vec3f sub_c(tvdb_vec3f a, tvdb_vec3f b) { return (tvdb_vec3f){a.x - b.x, a.y - b.y, a.z - b.z}; }
static inline tvdb_vec3f add_c(tvdb_vec3f a, tvdb_vec3f b) { return (tvdb_vec3f){a.x + b.x, a.y + b.y, a.z + b.z}; }
static inline tvdb_vec3f mul_c(tvdb_vec3f a, float s) { return (tvdb_vec3f){a.x * s, a.y * s, a.z * s}; }
static float dist_sq_c(tvdb_vec3f a, tvdb_vec3f b) { tvdb_vec3f d = sub_c(a, b); return dot_c(d, d); }
static float point_triangle_dist_sq_c(tvdb_vec3f p, tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c) {
  tvdb_vec3f ab = sub_c(b, a), ac = sub_c(c, a), ap = sub_c(p, a);
  float d1 = dot_c(ab, ap), d2 = dot_c(ac, ap);
  if (d1 <= 0.0f && d2 <= 0.0f) return dist_sq_c(p, a);
  tvdb_vec3f bp = sub_c(p, b);
  float d3 = dot_c(ab, bp), d4 = dot_c(ac, bp);
  if (d3 >= 0.0f && d4 <= d3) return dist_sq_c(p, b);
  float vc = d1 * d4 - d3 * d2;
  if (vc <= 0.0f && d1 >= 0.0f && d3 <= 0.0f) {
    float v = d1 / (d1 - d3);
    return dist_sq_c(p, add_c(a, mul_c(ab, v)));
  }
  tvdb_vec3f cp = sub_c(p, c);
  float d5 = dot_c(ab, cp), d6 = dot_c(ac, cp);
  if (d6 >= 0.0f && d5 <= d6) return dist_sq_c(p, c);
  float vb = d5 * d2 - d1 * d6;
  if (vb <= 0.0f && d2 >= 0.0f && d6 <= 0.0f) {
    float w = d2 / (d2 - d6);
    return dist_sq_c(p, add_c(a, mul_c(ac, w)));
  }
  float va = d3 * d6 - d5 * d4;
  if (va <= 0.0f && (d4 - d3) >= 0.0f && (d5 - d6) >= 0.0f) {
    float w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
    return dist_sq_c(p, add_c(b, mul_c(sub_c(c, b), w)));
  }
  float denom = 1.0f / (va + vb + vc);
  return dist_sq_c(p, add_c(add_c(a, mul_c(ab, vb * denom)), mul_c(ac, vc * denom)));
}

// VoxelPos, VoxelIdx, EdgeKey
static tvdb_vec3f voxel_pos_c(const tvdb_dense_grid* grid, int ix, int iy, int iz) {
    return (tvdb_vec3f){grid->ox + (ix + 0.5f) * grid->voxel_size,
                        grid->oy + (iy + 0.5f) * grid->voxel_size,
                        grid->oz + (iz + 0.5f) * grid->voxel_size};
}

static uint64_t voxel_idx_c(int nx, int ny, int ix, int iy, int iz) {
    return (uint64_t)ix + (uint64_t)iy * nx + (uint64_t)iz * nx * ny;
}

static uint64_t edge_key_c(uint64_t v0, uint64_t v1) {
    if (v0 > v1) { uint64_t temp = v0; v0 = v1; v1 = temp; }
    return (v0 << 32) | v1;
}

// Edge Cache
typedef struct {
    uint64_t key;
    uint32_t value;
} edge_cache_entry_t;

typedef struct {
    edge_cache_entry_t* entries;
    size_t count;
    size_t capacity;
} edge_cache_t;

static void edge_cache_init(edge_cache_t* cache, tvdb_arena_allocator_t* arena) {
    cache->count = 0;
    cache->capacity = 16;
    cache->entries = (edge_cache_entry_t*)arena_alloc_wrapper(arena, cache->capacity * sizeof(edge_cache_entry_t));
}

static uint32_t edge_cache_get_or_insert(edge_cache_t* cache, tvdb_arena_allocator_t* arena, uint64_t key, uint32_t new_value) {
    for (size_t i = 0; i < cache->count; ++i) {
        if (cache->entries[i].key == key) {
            return cache->entries[i].value;
        }
    }
    if (cache->count == cache->capacity) {
        size_t new_capacity = cache->capacity * 2;
        edge_cache_entry_t* new_entries = (edge_cache_entry_t*)arena_alloc_wrapper(arena, new_capacity * sizeof(edge_cache_entry_t));
        if (!new_entries) return 0;
        memcpy(new_entries, cache->entries, cache->count * sizeof(edge_cache_entry_t));
        cache->entries = new_entries;
        cache->capacity = new_capacity;
    }
    cache->entries[cache->count].key = key;
    cache->entries[cache->count].value = new_value;
    return cache->entries[cache->count++].value;
}

// Vertex Interpolation
static tvdb_vec3f vertex_interp_c(float iso, tvdb_vec3f p1, tvdb_vec3f p2, float v1, float v2) {
  if (fabsf(v1 - v2) < 1e-10f) return p1;
  float mu = (iso - v1) / (v2 - v1);
  return (tvdb_vec3f){p1.x + mu * (p2.x - p1.x), p1.y + mu * (p2.y - p1.y), p1.z + mu * (p2.z - p1.z)};
}

// C-compatible Edge Vertex Creation
static uint32_t get_or_create_edge_vertex_c(edge_cache_t* cache, tvdb_arena_allocator_t* arena,
                                            const tvdb_dense_grid* grid, float isovalue,
                                            tvdb_triangle_mesh* mesh,
                                            int x0, int y0, int z0, int x1, int y1, int z1) {
    uint64_t v0_flat = voxel_idx_c(grid->nx, grid->ny, x0, y0, z0);
    uint64_t v1_flat = voxel_idx_c(grid->nx, grid->ny, x1, y1, z1);
    uint64_t edge_key = edge_key_c(v0_flat, v1_flat);

    for (size_t i = 0; i < cache->count; ++i) {
        if (cache->entries[i].key == edge_key) return cache->entries[i].value;
    }

    tvdb_vec3f p0 = voxel_pos_c(grid, x0, y0, z0);
    tvdb_vec3f p1 = voxel_pos_c(grid, x1, y1, z1);
    float v0 = grid->data[voxel_idx_c(grid->nx, grid->ny, x0, y0, z0)];
    float v1 = grid->data[voxel_idx_c(grid->nx, grid->ny, x1, y1, z1)];
    tvdb_vec3f p = vertex_interp_c(isovalue, p0, p1, v0, v1);

    uint32_t idx = (uint32_t)mesh->vertex_count;
    if (mesh->vertex_count == mesh->vertex_capacity) {
        size_t new_cap = mesh->vertex_capacity * 2;
        tvdb_vec3f* new_verts = (tvdb_vec3f*)arena_alloc_wrapper(arena, new_cap * sizeof(tvdb_vec3f));
        if (!new_verts) return 0;
        memcpy(new_verts, mesh->vertices, mesh->vertex_count * sizeof(tvdb_vec3f));
        mesh->vertices = new_verts;
        mesh->vertex_capacity = new_cap;
    }
    mesh->vertices[mesh->vertex_count++] = p;
    
    if (edge_cache_get_or_insert(cache, arena, edge_key, idx) == 0 && cache->count == 0) return 0;
    return idx;
}

// -------------------------------------------------------------------------
// SDF -> mesh (marching cubes)
// -------------------------------------------------------------------------

// Marching-cubes corner-of-cube offsets and edge endpoint table.
static const int MC_CORNER_OFFSETS[8][3] = {
    {0,0,0},{1,0,0},{1,1,0},{0,1,0},
    {0,0,1},{1,0,1},{1,1,1},{0,1,1}
};

// MC edge -> (corner_a, corner_b) using the canonical lookup-table indexing.
static const int MC_EDGE_VERTS[12][2] = {
    {0,1},{1,2},{2,3},{3,0},
    {4,5},{5,6},{6,7},{7,4},
    {0,4},{1,5},{2,6},{3,7}
};

static bool ensure_mesh_capacity(tvdb_triangle_mesh* mesh,
                                 tvdb_arena_allocator_t* arena,
                                 size_t need_verts, size_t need_faces) {
    if (mesh->vertex_capacity < need_verts) {
        size_t cap = mesh->vertex_capacity ? mesh->vertex_capacity : 64;
        while (cap < need_verts) cap *= 2;
        tvdb_vec3f* nv = (tvdb_vec3f*)arena_alloc_wrapper(arena, cap * sizeof(tvdb_vec3f));
        if (!nv) return false;
        if (mesh->vertices) memcpy(nv, mesh->vertices, mesh->vertex_count * sizeof(tvdb_vec3f));
        // arena-backed memory is not freed; for malloc fall back, leak the
        // old buffer if arena==NULL (callers using malloc should size up-front).
        if (!arena && mesh->vertices) free(mesh->vertices);
        mesh->vertices = nv;
        mesh->vertex_capacity = cap;
    }
    if (mesh->face_capacity < need_faces) {
        size_t cap = mesh->face_capacity ? mesh->face_capacity : 64;
        while (cap < need_faces) cap *= 2;
        tvdb_triangle* nf = (tvdb_triangle*)arena_alloc_wrapper(arena, cap * sizeof(tvdb_triangle));
        if (!nf) return false;
        if (mesh->faces) memcpy(nf, mesh->faces, mesh->face_count * sizeof(tvdb_triangle));
        if (!arena && mesh->faces) free(mesh->faces);
        mesh->faces = nf;
        mesh->face_capacity = cap;
    }
    return true;
}

// MC_TRI_TABLE above only populates cube configurations 0..159; configs
// 160..255 are the complements (255-c) of 0..95 and were left implicitly
// zero-filled, which made the emit loop produce degenerate triangles for those
// cells. Complete the table once, lazily: a config and its bitwise complement
// share the same edge intersections (MC_EDGE_TABLE[c] == MC_EDGE_TABLE[255-c]),
// and the surface orientation flips, so triTable[255-c] is triTable[c] with
// each triangle's winding reversed. This is the standard MC complementary-case
// symmetry and yields a valid full table without hand-transcribing 96 rows.
static int g_mc_full_tri[256][16];
static int g_mc_full_tri_ready = 0;
static const int (*mc_full_tri_table(void))[16] {
    if (!g_mc_full_tri_ready) {
        for (int c = 0; c < 256; ++c)
            for (int k = 0; k < 16; ++k) g_mc_full_tri[c][k] = -1;
        for (int c = 0; c < 160; ++c)
            for (int k = 0; k < 16; ++k) g_mc_full_tri[c][k] = MC_TRI_TABLE[c][k];
        for (int c = 0; c <= 95; ++c) {
            int d = 255 - c;  // 160..255
            int w = 0;
            for (int i = 0; i < 16 && MC_TRI_TABLE[c][i] != -1; i += 3) {
                if (MC_TRI_TABLE[c][i+1] == -1 || MC_TRI_TABLE[c][i+2] == -1) break;
                g_mc_full_tri[d][w++] = MC_TRI_TABLE[c][i];
                g_mc_full_tri[d][w++] = MC_TRI_TABLE[c][i+2];  // reversed winding
                g_mc_full_tri[d][w++] = MC_TRI_TABLE[c][i+1];
            }
        }
        g_mc_full_tri_ready = 1;
    }
    return g_mc_full_tri;
}

bool tvdb_sdf_to_mesh(const tvdb_dense_grid* grid, float isovalue,
                      tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
    if (!grid || !grid->data || !mesh) return false;
    if (grid->nx < 2 || grid->ny < 2 || grid->nz < 2) return false;

    // The cache is keyed by edge-key (sorted pair of voxel flat indices); it
    // dedupes vertices that lie on shared cube edges.
    edge_cache_t cache;
    edge_cache_init(&cache, arena);

    // Pre-size the mesh buffers conservatively to avoid many reallocs.
    size_t init_verts = (size_t)grid->nx * grid->ny;
    size_t init_faces = init_verts * 2;
    if (mesh->vertex_capacity == 0) {
        if (!ensure_mesh_capacity(mesh, arena, init_verts, init_faces)) return false;
    }

    const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    for (int z = 0; z < nz - 1; ++z) {
      for (int y = 0; y < ny - 1; ++y) {
        for (int x = 0; x < nx - 1; ++x) {
            float vals[8];
            int corner_xyz[8][3];
            int cube_idx = 0;
            for (int i = 0; i < 8; ++i) {
                int cx = x + MC_CORNER_OFFSETS[i][0];
                int cy = y + MC_CORNER_OFFSETS[i][1];
                int cz = z + MC_CORNER_OFFSETS[i][2];
                corner_xyz[i][0] = cx;
                corner_xyz[i][1] = cy;
                corner_xyz[i][2] = cz;
                vals[i] = grid->data[voxel_idx_c(nx, ny, cx, cy, cz)];
                if (vals[i] < isovalue) cube_idx |= (1 << i);
            }
            int edges = MC_EDGE_TABLE[cube_idx];
            if (edges == 0) continue;

            // Compute (or fetch from cache) one vertex per active edge.
            uint32_t edge_vert_idx[12] = {0};
            for (int e = 0; e < 12; ++e) {
                if (!(edges & (1 << e))) continue;
                int a = MC_EDGE_VERTS[e][0];
                int b = MC_EDGE_VERTS[e][1];
                edge_vert_idx[e] = get_or_create_edge_vertex_c(
                    &cache, arena, grid, isovalue, mesh,
                    corner_xyz[a][0], corner_xyz[a][1], corner_xyz[a][2],
                    corner_xyz[b][0], corner_xyz[b][1], corner_xyz[b][2]);
            }

            // Emit triangles for this cube (full 256-entry table).
            const int* tri = mc_full_tri_table()[cube_idx];
            for (int i = 0; i < 16 && tri[i] != -1; i += 3) {
                if (tri[i+1] == -1 || tri[i+2] == -1) break;
                if (mesh->face_count == mesh->face_capacity) {
                    if (!ensure_mesh_capacity(mesh, arena,
                            mesh->vertex_capacity,
                            mesh->face_capacity ? mesh->face_capacity * 2 : 64))
                        return false;
                }
                tvdb_triangle t;
                t.v0 = edge_vert_idx[tri[i]];
                t.v1 = edge_vert_idx[tri[i+1]];
                t.v2 = edge_vert_idx[tri[i+2]];
                mesh->faces[mesh->face_count++] = t;
            }
        }
      }
    }
    return true;
}

// -------------------------------------------------------------------------
// Mesh -> SDF (closest-triangle, signed via face normal)
// -------------------------------------------------------------------------
//
// For each voxel, compute distance to nearest triangle; sign comes from
// dot((voxel - closest_point), triangle_normal). This is the classic
// "pseudo-normal-free" approach: simple, robust for moderately well-formed
// closed meshes, but can have sign artifacts at sharp edges/vertices.
//
// Distance is clamped to ±band_width.

static tvdb_vec3f tri_closest_point_c(tvdb_vec3f p, tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c) {
    // Same case analysis as point_triangle_dist_sq_c, but returning the point.
    tvdb_vec3f ab = sub_c(b, a), ac = sub_c(c, a), ap = sub_c(p, a);
    float d1 = dot_c(ab, ap), d2 = dot_c(ac, ap);
    if (d1 <= 0.0f && d2 <= 0.0f) return a;
    tvdb_vec3f bp = sub_c(p, b);
    float d3 = dot_c(ab, bp), d4 = dot_c(ac, bp);
    if (d3 >= 0.0f && d4 <= d3) return b;
    float vc = d1 * d4 - d3 * d2;
    if (vc <= 0.0f && d1 >= 0.0f && d3 <= 0.0f) {
        float v = d1 / (d1 - d3);
        return add_c(a, mul_c(ab, v));
    }
    tvdb_vec3f cp = sub_c(p, c);
    float d5 = dot_c(ab, cp), d6 = dot_c(ac, cp);
    if (d6 >= 0.0f && d5 <= d6) return c;
    float vb = d5 * d2 - d1 * d6;
    if (vb <= 0.0f && d2 >= 0.0f && d6 <= 0.0f) {
        float w = d2 / (d2 - d6);
        return add_c(a, mul_c(ac, w));
    }
    float va = d3 * d6 - d5 * d4;
    if (va <= 0.0f && (d4 - d3) >= 0.0f && (d5 - d6) >= 0.0f) {
        float w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
        return add_c(b, mul_c(sub_c(c, b), w));
    }
    float denom = 1.0f / (va + vb + vc);
    return add_c(add_c(a, mul_c(ab, vb * denom)), mul_c(ac, vc * denom));
}

static tvdb_vec3f cross_c(tvdb_vec3f a, tvdb_vec3f b) {
    return (tvdb_vec3f){a.y * b.z - a.z * b.y,
                        a.z * b.x - a.x * b.z,
                        a.x * b.y - a.y * b.x};
}

static tvdb_vec3f normalize_c(tvdb_vec3f v) {
    float L = sqrtf(dot_c(v, v));
    if (L < 1e-30f) return (tvdb_vec3f){0, 0, 0};
    return mul_c(v, 1.0f / L);
}

bool tvdb_mesh_to_sdf(const tvdb_triangle_mesh* mesh, float voxel_size,
                      float band_width, tvdb_dense_grid* grid,
                      tvdb_arena_allocator_t* arena) {
    if (!mesh || !grid || mesh->vertex_count == 0 || mesh->face_count == 0) return false;
    if (voxel_size <= 0.0f || band_width <= 0.0f) return false;

    // World-space bounding box of the mesh, padded by band_width.
    tvdb_vec3f bb_min = mesh->vertices[0], bb_max = mesh->vertices[0];
    for (size_t i = 1; i < mesh->vertex_count; ++i) {
        tvdb_vec3f v = mesh->vertices[i];
        if (v.x < bb_min.x) bb_min.x = v.x; if (v.x > bb_max.x) bb_max.x = v.x;
        if (v.y < bb_min.y) bb_min.y = v.y; if (v.y > bb_max.y) bb_max.y = v.y;
        if (v.z < bb_min.z) bb_min.z = v.z; if (v.z > bb_max.z) bb_max.z = v.z;
    }
    bb_min.x -= band_width; bb_min.y -= band_width; bb_min.z -= band_width;
    bb_max.x += band_width; bb_max.y += band_width; bb_max.z += band_width;

    int nx = (int)ceilf((bb_max.x - bb_min.x) / voxel_size);
    int ny = (int)ceilf((bb_max.y - bb_min.y) / voxel_size);
    int nz = (int)ceilf((bb_max.z - bb_min.z) / voxel_size);
    if (nx < 1) nx = 1; if (ny < 1) ny = 1; if (nz < 1) nz = 1;
    if (nx > TVDB_MAX_GRID_DIM || ny > TVDB_MAX_GRID_DIM || nz > TVDB_MAX_GRID_DIM)
        return false;

    grid->nx = nx; grid->ny = ny; grid->nz = nz;
    grid->voxel_size = voxel_size;
    grid->ox = bb_min.x; grid->oy = bb_min.y; grid->oz = bb_min.z;
    size_t total = (size_t)nx * ny * nz;
    grid->data = (float*)arena_alloc_wrapper(arena, total * sizeof(float));
    if (!grid->data) return false;

    // Pre-compute triangle data for speed.
    size_t nf = mesh->face_count;
    tvdb_vec3f* tri_n = (tvdb_vec3f*)arena_alloc_wrapper(arena, nf * sizeof(tvdb_vec3f));
    if (!tri_n) return false;
    for (size_t f = 0; f < nf; ++f) {
        tvdb_vec3f a = mesh->vertices[mesh->faces[f].v0];
        tvdb_vec3f b = mesh->vertices[mesh->faces[f].v1];
        tvdb_vec3f c = mesh->vertices[mesh->faces[f].v2];
        tri_n[f] = normalize_c(cross_c(sub_c(b, a), sub_c(c, a)));
    }

    for (int z = 0; z < nz; ++z) {
      for (int y = 0; y < ny; ++y) {
        for (int x = 0; x < nx; ++x) {
            tvdb_vec3f p = voxel_pos_c(grid, x, y, z);
            float best_dsq = INFINITY;
            tvdb_vec3f best_cp = {0, 0, 0};
            tvdb_vec3f best_n  = {0, 0, 0};
            for (size_t f = 0; f < nf; ++f) {
                tvdb_vec3f a = mesh->vertices[mesh->faces[f].v0];
                tvdb_vec3f b = mesh->vertices[mesh->faces[f].v1];
                tvdb_vec3f c = mesh->vertices[mesh->faces[f].v2];
                tvdb_vec3f cp = tri_closest_point_c(p, a, b, c);
                tvdb_vec3f d = sub_c(p, cp);
                float dsq = dot_c(d, d);
                if (dsq < best_dsq) {
                    best_dsq = dsq;
                    best_cp = cp;
                    best_n = tri_n[f];
                }
            }
            float dist = sqrtf(best_dsq);
            float s = dot_c(sub_c(p, best_cp), best_n) >= 0.0f ? 1.0f : -1.0f;
            float v = s * dist;
            if (v >  band_width) v =  band_width;
            if (v < -band_width) v = -band_width;
            grid->data[voxel_idx_c(nx, ny, x, y, z)] = v;
        }
      }
    }
    return true;
}

// -------------------------------------------------------------------------
// Mesh -> SDF -> Mesh (remeshing for manifold-ness)
// -------------------------------------------------------------------------

bool tvdb_make_manifold(const tvdb_triangle_mesh* input, double resolution,
                        double isovalue, tvdb_triangle_mesh* output,
                        tvdb_arena_allocator_t* arena) {
    if (!input || !output || resolution <= 0.0) return false;

    tvdb_dense_grid grid;
    grid.data = NULL;
    float band = (float)(resolution * 4.0);
    if (!tvdb_mesh_to_sdf(input, (float)resolution, band, &grid, arena)) return false;
    bool ok = tvdb_sdf_to_mesh(&grid, (float)isovalue, output, arena);
    if (!arena) tvdb_dense_grid_free(&grid);
    return ok;
}

// -------------------------------------------------------------------------
// _vdb variants (sign_method is currently advisory; the implementation uses
// closest-triangle pseudo-normal sign regardless).
// -------------------------------------------------------------------------

bool tvdb_mesh_to_sdf_vdb(const tvdb_triangle_mesh* mesh, float voxel_size,
                          float band_width, tvdb_dense_grid* grid,
                          tvdb_sign_method sign_method,
                          tvdb_arena_allocator_t* arena) {
    (void)sign_method;
    return tvdb_mesh_to_sdf(mesh, voxel_size, band_width, grid, arena);
}

bool tvdb_make_manifold_vdb(const tvdb_triangle_mesh* input, double resolution,
                            double isovalue, tvdb_triangle_mesh* output,
                            tvdb_sign_method sign_method,
                            tvdb_arena_allocator_t* arena) {
    (void)sign_method;
    return tvdb_make_manifold(input, resolution, isovalue, output, arena);
}
