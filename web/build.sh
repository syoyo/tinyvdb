#!/bin/bash
#
# Build TinyVDB WASM module using Emscripten.
#
# Prerequisites:
#   - Emscripten SDK installed and activated (source emsdk_env.sh)
#
# Usage:
#   cd web && ./build.sh [Release|Debug]
#

set -e

BUILD_TYPE="${1:-Release}"
BUILD_DIR="build-wasm"

if ! command -v emcmake &> /dev/null; then
    echo "Error: emcmake not found. Activate Emscripten SDK first:"
    echo "  source /path/to/emsdk/emsdk_env.sh"
    exit 1
fi

echo "Building TinyVDB WASM (${BUILD_TYPE})..."

rm -rf "${BUILD_DIR}"
mkdir -p "${BUILD_DIR}"

emcmake cmake -B "${BUILD_DIR}" \
    -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" \
    .

emmake cmake --build "${BUILD_DIR}" -j$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

echo ""
echo "Build complete. Output:"
ls -lh "${BUILD_DIR}/tinyvdb.js" "${BUILD_DIR}/tinyvdb.wasm"
echo ""
echo "Usage in browser:"
echo "  import TinyVDB from './tinyvdb.js';"
echo "  const tv = await TinyVDB();"
