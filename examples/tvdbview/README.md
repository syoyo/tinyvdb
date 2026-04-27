# tvdbview

Minimal OpenGL viewer for TinyVDB `.vdb` files.

## Build

```sh
cmake -S . -B build-tvdbview -DTINYVDB_BUILD_EXAMPLES=ON -DTINYVDB_BUILD_TVDBVIEW=ON
cmake --build build-tvdbview --target tvdbview
```

## Run

```sh
./build-tvdbview/examples/tvdbview/tvdbview smoke.vdb
```

## Controls

- Left drag: orbit camera
- Middle or right drag: pan camera
- Mouse wheel: zoom
- `O`: open a VDB file with native file dialog
- `V`: cycle volume/grid display
- `C`: cycle color mode
- `[` / `]`: decrease/increase density gain
- `S`: toggle SDF fog interpretation
- `R`: reset camera
- `H`: print controls
- `Esc`: quit
