#!/bin/bash
#
# Build single-file zstd.c and zstd.h from the facebook/zstd repository.
# Outputs to deps/zstd.c and deps/zstd.h.
#
# Usage:
#   cd <tinyvdbio root>
#   bash scripts/build-zstd-single-file.sh
#
# Requirements: git, python3
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
TMP_DIR="$ROOT_DIR/tmp"
DEPS_DIR="$ROOT_DIR/deps"
ZSTD_REPO="https://github.com/facebook/zstd.git"
ZSTD_TAG="v1.5.7"  # Latest stable release

echo "=== Building single-file zstd ($ZSTD_TAG) ==="

# Clone zstd to tmp/
mkdir -p "$TMP_DIR"
if [ -d "$TMP_DIR/zstd" ]; then
    echo "Removing existing tmp/zstd..."
    rm -rf "$TMP_DIR/zstd"
fi

echo "Cloning $ZSTD_REPO ($ZSTD_TAG) ..."
git clone --depth 1 --branch "$ZSTD_TAG" "$ZSTD_REPO" "$TMP_DIR/zstd"

# Print version
ZSTD_VERSION=$(grep -oP 'ZSTD_VERSION_MAJOR\s+\K\d+' "$TMP_DIR/zstd/lib/zstd.h").$(grep -oP 'ZSTD_VERSION_MINOR\s+\K\d+' "$TMP_DIR/zstd/lib/zstd.h").$(grep -oP 'ZSTD_VERSION_RELEASE\s+\K\d+' "$TMP_DIR/zstd/lib/zstd.h")
echo "Zstd version: $ZSTD_VERSION"

# Build single-file zstd.c using the upstream combine.py tool
cd "$TMP_DIR/zstd/build/single_file_libs"
echo "Generating zstd.c ..."
python3 combine.py \
    -r ../../lib \
    -x legacy/zstd_legacy.h \
    -k zstd.h \
    -o zstd.c \
    zstd-in.c

# Copy to deps/
mkdir -p "$DEPS_DIR"
cp "$TMP_DIR/zstd/build/single_file_libs/zstd.c" "$DEPS_DIR/zstd.c"
cp "$TMP_DIR/zstd/lib/zstd.h" "$DEPS_DIR/zstd.h"
cp "$TMP_DIR/zstd/lib/zstd_errors.h" "$DEPS_DIR/zstd_errors.h"

# Fix include path: zstd.c references "../zstd.h" but both files live in deps/
sed -i 's|#include "../zstd.h"|#include "zstd.h"|g' "$DEPS_DIR/zstd.c"

echo ""
echo "=== Done ==="
echo "  deps/zstd.c  $(wc -l < "$DEPS_DIR/zstd.c") lines"
echo "  deps/zstd.h  $(wc -l < "$DEPS_DIR/zstd.h") lines"
echo "  Zstd version: $ZSTD_VERSION"
echo "  License: BSD (Meta Platforms, Inc.)"

# Cleanup
echo ""
echo "Cleaning up tmp/zstd ..."
rm -rf "$TMP_DIR/zstd"
echo "Done."
