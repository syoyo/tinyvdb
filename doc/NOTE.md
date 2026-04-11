# Note on .vdb format

```
+--------------------------------+
|  Header                        |
+--------------------------------+
|  num meta data(4 bytes)        |
+--------------------------------+
|                                |
|    Meta data x N               |
|                                |
+--------------------------------+
|  num grid descriptors(4 bytes) |
+--------------------------------+
|                                |
|    Grid Descriptors x N      ------+
|                                |   |
+--------------------------------+   | Grid byte offset
|                                |   |
|                                |<--+
|  Grid data x NumGrids          |
|                                |
|                                |
+--------------------------------+
|                                |
|  Voxel data                    |
|                                |
+--------------------------------+
```

## Header

OpenVDB stores data in little endian manner(e.g. endian used in x86).
TinyVDB supports version 220 or later.

* 8 byte : magic number
* 4 byte : version(220~224 are supported in TinyVDB)
* 4 + 4 byte : major and minor version
* 1 byte : Grid offset flag(must be true)
* optional : 1 byte : Global compression flag(version 220 ~ 221). Compression flag is stored per grid for 222 or later
* 36 bytes : UUID

## Meta data

Optional.

## Grid descriptor

* unique name(string)
* grid type(string)
* instance parent name(string)
* Grid byte offset(8bytes)
* Block byte offset(8bytes)
* End byte offset(8bytes)

Describe grid structure(e.g. tree structure) and has some info(e.g. unique grid name)

### Grid type

Grid structure is arbitrary, but in most case its composed of 3 hierarches. 5(intermediate), 4(intermediate) and 3(leaf).
Grid structure is described in string.
Supported type in TinyVDB is `Tree_float_5_4_3`.
Optional: half precion if the typename has suffix `_HalfFloat`(e.g, `Tree_float_5_4_3_HalfFloat`)

### End byte offset

End byte offset points the end of this grid descripor, which means the beginning of the next grid descriptor.

## Grid

* (optional) 4 byte: Per-grid compression flag(version 222~)
* Metadata
* Transform

### Instanced grid

T.B.W.

### non-instanced grid

* Topology
* Buffer

## Mask

simply bitmask. may be compressed using zlib(?).


EoL.
