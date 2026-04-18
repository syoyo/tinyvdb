#!/bin/bash
set -e

# regression_test.sh
# Usage: ./scripts/regression_test.sh <vdbdump_path>

VDBDUMP=$1
if [ -z "$VDBDUMP" ]; then
    echo "Usage: $0 <vdbdump_binary_path>"
    exit 1
fi

DATA_DIR="data"
TMP_DIR="/tmp/tinyvdb_regression"
mkdir -p "$TMP_DIR"

FAILED=0
TOTAL=0

# Find all VDB files in data dir
VDB_FILES=$(find "$DATA_DIR" -name "*.vdb")

for INFILE in $VDB_FILES; do
    TOTAL=$((TOTAL + 1))
    echo "Testing $INFILE..."
    
    OUTFILE="$TMP_DIR/$(basename "$INFILE")"
    
    # Round-trip
    "$VDBDUMP" "$INFILE" --write "$OUTFILE" > /dev/null
    
    # Compare with vdb_print
    # We use -metadata flag to check metadata too, but it might differ
    # For now just check the basic grid info
    vdb_print "$INFILE" > "$TMP_DIR/in.txt"
    vdb_print "$OUTFILE" > "$TMP_DIR/out.txt"
    
    if diff "$TMP_DIR/in.txt" "$TMP_DIR/out.txt" > /dev/null; then
        echo "  PASS"
    else
        echo "  FAIL: Grid info mismatch"
        diff -u "$TMP_DIR/in.txt" "$TMP_DIR/out.txt" || true
        FAILED=$((FAILED + 1))
    fi
done

echo ""
echo "Summary: $((TOTAL - FAILED))/$TOTAL passed"

if [ $FAILED -ne 0 ]; then
    exit 1
fi
exit 0
