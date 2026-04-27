# tvdbview

Minimal OpenGL viewer for TinyVDB `.vdb` files.

The viewer has an on-screen HUD and an ImGui control panel for selecting grids,
changing render/color modes, adjusting density gain, controlling slice/clip
settings, toggling bounding boxes, saving screenshots, and managing camera
presets/bookmarks.

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
- `0`-`9`: select VDB attribute/grid by index
- `X` / `Y` / `Z`: enable slice view along the selected axis
- `\`: disable slice view
- `,` / `.`: move the slice plane
- `-` / `=`: decrease/increase slice thickness
- `K`: toggle clip box
- `U` / `J`: tighten/loosen clip box
- `I` / `L` / `B`: toggle internal boxes, leaf boxes, dense bounds
- `V`: cycle volume/grid display
- `C`: cycle color mode
- `[` / `]`: decrease/increase density gain
- `P`: save a PNG screenshot
- `F`: frame selected grid
- `F1` / `F2` / `F3`: front/top/side camera presets
- `Ctrl+F1`-`Ctrl+F3`: save camera bookmarks
- `Shift+F1`-`Shift+F3`: load camera bookmarks
- `S`: toggle SDF fog interpretation
- `R`: reset camera
- `H`: print controls
- `Esc`: quit
