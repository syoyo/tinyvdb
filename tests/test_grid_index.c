// Theme D: coordinate utilities and point/coordinate spatial queries.

#include "tinyvdb_grid_index.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static int fails = 0;
#define EXPECT(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fails; } \
} while (0)

int main(void) {
  const float vs[3] = { 0.1f, 0.2f, 0.05f };
  const float org[3] = { -1.0f, 0.5f, 2.0f };

  // ---- world <-> ijk round trip ----
  {
    int32_t ijk[3] = { 3, -2, 17 };
    float w[3]; tvdb_ijk_to_world(ijk, 1, vs, org, w);
    // world center of voxel (3,-2,17)
    EXPECT(fabsf(w[0] - (org[0] + 3.5f*vs[0])) < 1e-6f, "ijk_to_world x");
    EXPECT(fabsf(w[1] - (org[1] + -1.5f*vs[1])) < 1e-6f, "ijk_to_world y");
    int32_t back[3]; tvdb_world_to_ijk(w, 1, vs, org, back);
    EXPECT(back[0]==3 && back[1]==-2 && back[2]==17, "world_to_ijk round trip");
  }

  // ---- Morton encode/decode round trip (incl. negatives) ----
  {
    int32_t coords[5][3] = { {0,0,0}, {1,2,3}, {-5,7,-9}, {1000,-1000,500}, {-1,-1,-1} };
    for (int i = 0; i < 5; ++i) {
      uint64_t code = tvdb_morton_encode(coords[i][0], coords[i][1], coords[i][2]);
      int32_t x,y,z; tvdb_morton_decode(code, &x,&y,&z);
      EXPECT(x==coords[i][0] && y==coords[i][1] && z==coords[i][2], "morton round trip");
    }
  }

  // ---- voxelize a point cloud (dedup into unique cells) ----
  {
    // 4 points, two land in the same voxel.
    float pts[4][3] = {
      { -1.0f + 0.05f, 0.5f + 0.05f, 2.0f + 0.01f },   // voxel (0,0,0)
      { -1.0f + 0.07f, 0.5f + 0.09f, 2.0f + 0.02f },   // voxel (0,0,0) too
      { -1.0f + 0.15f, 0.5f + 0.05f, 2.0f + 0.01f },   // voxel (1,0,0)
      { -1.0f + 0.05f, 0.5f + 0.25f, 2.0f + 0.01f },   // voxel (0,1,0)
    };
    int32_t* coords = NULL; size_t cnt = 0;
    EXPECT(tvdb_voxelize_points(&pts[0][0], 4, vs, org, &coords, &cnt), "voxelize ok");
    EXPECT(cnt == 3, "voxelize dedups to 3 unique cells");
    free(coords);
  }

  // ---- coords_in_set / ijk_to_index / points_in_set ----
  {
    int32_t active[3][3] = { {0,0,0}, {5,5,5}, {-3,2,1} };
    int32_t query[4][3] = { {5,5,5}, {0,0,0}, {9,9,9}, {-3,2,1} };
    uint8_t in[4]; int64_t idx[4];
    EXPECT(tvdb_coords_in_set(&active[0][0], 3, &query[0][0], 4, in), "coords_in_set ok");
    EXPECT(in[0]==1 && in[1]==1 && in[2]==0 && in[3]==1, "coords_in_set membership");
    EXPECT(tvdb_ijk_to_index(&active[0][0], 3, &query[0][0], 4, idx), "ijk_to_index ok");
    EXPECT(idx[0]==1 && idx[1]==0 && idx[2]==-1 && idx[3]==2, "ijk_to_index values");

    // A point inside voxel (5,5,5) is "in"; a far point is not.
    float p[2][3] = {
      { org[0] + (5+0.3f)*vs[0], org[1] + (5+0.3f)*vs[1], org[2] + (5+0.3f)*vs[2] },
      { org[0] + (50)*vs[0],     org[1],                  org[2] },
    };
    uint8_t pin[2];
    EXPECT(tvdb_points_in_set(&p[0][0], 2, vs, org, &active[0][0], 3, pin), "points_in_set ok");
    EXPECT(pin[0]==1 && pin[1]==0, "points_in_set membership");
  }

  // ---- neighbor counts ----
  {
    // A 2x2x2 block: each voxel has 3 face-neighbors inside the block.
    int32_t blk[8][3];
    int b = 0;
    for (int z=0;z<2;++z) for (int y=0;y<2;++y) for (int x=0;x<2;++x) { blk[b][0]=x; blk[b][1]=y; blk[b][2]=z; ++b; }
    int32_t cnt6[8];
    EXPECT(tvdb_neighbor_counts(&blk[0][0], 8, 6, cnt6), "neighbor_counts ok");
    int allthree = 1; for (int i=0;i<8;++i) if (cnt6[i]!=3) allthree=0;
    EXPECT(allthree, "2x2x2 block: 3 face-neighbors each");
    int32_t cnt26[8];
    tvdb_neighbor_counts(&blk[0][0], 8, 26, cnt26);
    int allseven = 1; for (int i=0;i<8;++i) if (cnt26[i]!=7) allseven=0;
    EXPECT(allseven, "2x2x2 block: 7 26-neighbors each");
  }

  if (fails) { fprintf(stderr, "%d FAILURES\n", fails); return 1; }
  printf("All grid-index tests passed.\n");
  return 0;
}
