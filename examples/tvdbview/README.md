# tvdbview

Minimal OpenGL viewer for TinyVDB `.vdb` files.

The viewer has an on-screen HUD and an ImGui control panel for selecting grids,
changing render/color modes, adjusting density gain, controlling slice/clip
settings, toggling bounding boxes, saving screenshots, and managing camera
presets/bookmarks. It also supports value-window controls, per-grid histogram
stats, command-line startup state, and Ctrl-click value probing.

## Build

```sh
cmake -S . -B build-tvdbview -DTINYVDB_BUILD_EXAMPLES=ON -DTINYVDB_BUILD_TVDBVIEW=ON
cmake --build build-tvdbview --target tvdbview
```

## Run

```sh
./build-tvdbview/tvdbview smoke.vdb
```

Useful command-line options:

```sh
./build-tvdbview/tvdbview smoke.vdb --grid density --color blackbody --gain 4
./build-tvdbview/tvdbview smoke.vdb --display grid --no-internal-boxes
./build-tvdbview/tvdbview smoke.vdb --window 0.01:1.5 --gamma 0.8 --steps 256
./build-tvdbview/tvdbview smoke.vdb --ray mip --color jet
./build-tvdbview/tvdbview smoke.vdb --ray iso --iso 0.35 --color blackbody --shade-strength 0.8
./build-tvdbview/tvdbview smoke.vdb --ray pathtrace --pt-backend vulkan --pt-scale 2 --sun 35:45 --pt-depth 2
./build-tvdbview/tvdbview smoke.vdb --ray pathtrace --pt-backend cpu --pt-spp 8 --hide-hud --hide-panel --capture pt.png --quit
./build-tvdbview/tvdbview smoke.vdb --window-percentile 1:99 --clip-active
./build-tvdbview/tvdbview smoke.vdb --slice z:0.5:0.03 --clip 0,0,0:1,1,0.6
./build-tvdbview/tvdbview smoke.vdb --size 1920x1080 --hide-hud --hide-panel --capture frame.png --quit
```

`--grid` accepts a grid index or exact grid name. `--color` accepts `density`,
`jet`, `blackbody`, or `vector`. `--window min:max` enables manual value
windowing, while `--window-percentile lo:hi` derives a value window from the
selected grid. `--clip-active` clips to non-background dense cells. `--invert`,
`--opacity-power`, `--steps`, `--ray composite|mip|iso|pathtrace`, and the
shading flags (`--shade`, `--no-shade`, `--shade-strength`, `--light`) further
shape the rendered result. `--ray pathtrace` enables the progressive volumetric
path tracer with sun/sky lighting. It can use a runtime-loaded Vulkan compute
backend, an OpenGL compute backend, or the CPU renderer; use
`--pt-backend auto|gpu|vulkan|cpu`, `--pt-scale`, `--pt-rows`, `--pt-depth`,
`--pt-spp`, `--sun`, `--sun-strength`, `--sky-strength`, and `--pt-albedo` to control
quality and lighting. Vulkan is resolved at runtime from `libvulkan` and is not
linked through CMake; the Vulkan compute shader source is kept in
`vulkan_pathtrace.comp`. CMake regenerates the SPIR-V include when
`glslangValidator` and `xxd` are available, otherwise it uses the checked-in
`vulkan_pathtrace_spv.inc` fallback. Path-trace captures with hidden HUD/panel
save the progressive render buffer directly. The tabbed control panel includes a
`Copy command` button to recreate the current display state, including camera,
window size, and capture settings, from the command line.

## Controls

- Left drag: orbit camera
- Middle or right drag: pan camera
- Mouse wheel: zoom
- Ctrl+left click: probe selected grid value; the panel can use midpoint or
  strongest visible sample along the clicked ray
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
- `M`: cycle ray/pathtrace mode
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
