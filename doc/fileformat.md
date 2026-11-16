# OpenVDB file format

## Header

```
typedef struct {
  uint32_t file_version;
  uint32_t major_version;
  uint32_t minor_version;
  // bool has_grid_offsets;
  bool is_compressed;
  std::string uuid;
  uint64_t offset_to_data;  // Byte offset to VDB data
} VDBHeader;
```

* [0:7] Header magic number(8 bytes)
* [8:11] Version(4 bytes)
  * version >= 211
    * major_version(uint32_t)
    * minor_version(uint32_t)
  * version >= 212
    * has_grid_offsets(char)
  * 220 <= version < 222
    * is_compressed(char)
  * uuid(32 chars + 4 hyphens('-') = 36 bytes)

## Version

220: `OPENVDB_FILE_VERSION_SELECTIVE_COMPRESSION`

## Tree structure

Usually `FloatTree`(`tree::Tree4<float,       5, 4, 3>::Type`

* 5 : Intermediate grid level 0. (32x32x32 cells)
* 4 : Intermediate grid level 1. (16x16x16 cells)
* 3 : Leaf grid (8x8x8 cells)

So we could represent 4096x4096x4096 voxels 

Each grid is composed of `(2^N)^3` cells.


## Type

* float(32bit float)
* half(16bit half float)

## Intermediate

T.B.W.

## Leaf

* bitmask
* actual data(data is tightly packed) 
  * `sizeof(T) * bitmask.countOn()` 
