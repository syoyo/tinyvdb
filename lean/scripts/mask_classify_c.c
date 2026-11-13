/* Differential harness: dump the mask-compression classification emitted by
 * the C writer (`tvdb__write_mask_values`) for every synthetic 8-slot node.
 *
 * Enumerates all value masks (0..255) and, for each, every assignment of a
 * five-symbol alphabet to the inactive slots (the active slots hold the
 * background, which the classifier ignores). The alphabet is
 *
 *   bg, -bg, 2.5f, 3.5f, 4.5f      (bg = 1.5f)
 *
 * so "+bg vs -bg vs other" is fully exercised, and count == 3 is reachable.
 * Total: sum_j C(8, j) * 5^j = 6^8 = 1,679,616 nodes.
 *
 * One line per node:
 *   mask assign code v0hex v1hex selhex
 * where `assign` enumerates the inactive-slot assignments in base-5
 * (inactive slots in increasing order, least significant digit first),
 * `code` is the wire code byte (0-6), `v0hex`/`v1hex` are the eight
 * lowercase hex digits of the stored inactive value(s) at full precision
 * ("-" when the code carries no such value) and `selhex` the two hex
 * digits of the selection-mask byte ("-" when the code carries none).
 *
 * The payload written after the classification prefix (the chunk header and
 * the packed values) is not compared; the reconstructed values are covered by
 * the Lean round-trip theorems instead.
 *
 * Compile: cc -std=c11 -O2 -I<repo>/src mask_classify_c.c -o mask_classify_c
 */
/* TinyVDB I/O with the implementation enabled, as in the C tests. */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L /* ftruncate used inside tvdb_file_save */
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint32_t SYM[5] = {
    0x3FC00000u, /*  1.5f  (the background) */
    0xBFC00000u, /* -1.5f  (-bg)            */
    0x40200000u, /*  2.5f                     */
    0x40600000u, /*  3.5f                     */
    0x40800000u, /*  4.5f                     */
};
#define BG_BITS 0x3FC00000u

static void *mc_malloc(size_t n, void *ctx) { (void)ctx; return malloc(n ? n : 1); }
static void *mc_realloc(void *p, size_t old_size, size_t new_size, void *ctx) {
    (void)old_size; (void)ctx; return realloc(p, new_size ? new_size : 1);
}
static void mc_free(void *p, size_t size, void *ctx) { (void)size; (void)ctx; free(p); }

static int flag_has_val0(uint8_t flag) {
    return flag == TVDB_NO_MASK_AND_ONE_INACTIVE_VAL ||
           flag == TVDB_MASK_AND_ONE_INACTIVE_VAL ||
           flag == TVDB_MASK_AND_TWO_INACTIVE_VALS;
}
static int flag_has_val1(uint8_t flag) {
    return flag == TVDB_MASK_AND_TWO_INACTIVE_VALS;
}
static int flag_has_sel(uint8_t flag) {
    return flag == TVDB_MASK_AND_NO_INACTIVE_VALS ||
           flag == TVDB_MASK_AND_ONE_INACTIVE_VAL ||
           flag == TVDB_MASK_AND_TWO_INACTIVE_VALS;
}

int main(void) {
    tvdb_allocator_t alloc = { mc_malloc, mc_realloc, mc_free, NULL };

    tvdb_nodemask_t value_mask;
    tvdb__nodemask_init(&value_mask);
    if (!tvdb__nodemask_alloc(&value_mask, 1, &alloc)) {
        fprintf(stderr, "mask alloc failed\n");
        return 1;
    }

    tvdb_value_t background;
    memset(&background, 0, sizeof background);
    background.type = TVDB_VALUE_FLOAT;
    background.u.f = 1.5f;

    for (int mask = 0; mask < 256; mask++) {
        int inactive[8];
        int nin = 0;
        for (int i = 0; i < 8; i++) {
            if (!((mask >> i) & 1)) inactive[nin++] = i;
        }
        size_t total = 1;
        for (int i = 0; i < nin; i++) total *= 5;

        /* One output buffer per mask row; keeps stdout writes coarse. */
        size_t cap = total * 48 + 64, len = 0;
        char *out = (char *)malloc(cap);
        if (!out) { fprintf(stderr, "oom\n"); return 1; }

        for (size_t assign = 0; assign < total; assign++) {
            uint8_t slots[8 * 4];
            memset(slots, 0, sizeof slots);
            uint32_t word[8];
            for (int i = 0; i < 8; i++) word[i] = BG_BITS;
            size_t a = assign;
            for (int i = 0; i < nin; i++) {
                word[inactive[i]] = SYM[a % 5];
                a /= 5;
            }
            for (int i = 0; i < 8; i++) memcpy(slots + i * 4, &word[i], 4);

            value_mask.bits.data[0] = (uint8_t)mask;

            tvdb__sw_t sw;
            tvdb__sw_init(&sw, &alloc);
            tvdb_error_t err;
            memset(&err, 0, sizeof err);
            tvdb_status_t st = tvdb__write_mask_values(
                &sw, TVDB_COMPRESS_ACTIVE_MASK, background, 8,
                TVDB_VALUE_FLOAT, &value_mask, slots,
                /*half_precision=*/0, &alloc, &err);
            if (st != TVDB_OK) {
                fprintf(stderr, "write failed mask=%d assign=%zu: %s\n",
                        mask, assign, err.message);
                return 1;
            }

            /* Parse the classification prefix (layout is fixed for
               log2dim == 1, vsize == 4). The file is always little-endian,
               so print the stored bytes in stored order: host-independent
               and identical to the Lean side's `hexLE`. */
            const uint8_t *d = sw.data;
            size_t off = 0;
            uint8_t flag = d[off++];
            char v0hex[9] = "-", v1hex[9] = "-", selhex[3] = "-";
            if (flag_has_val0(flag)) {
                snprintf(v0hex, sizeof v0hex, "%02x%02x%02x%02x",
                         d[off], d[off + 1], d[off + 2], d[off + 3]);
                off += 4;
            }
            if (flag_has_val1(flag)) {
                snprintf(v1hex, sizeof v1hex, "%02x%02x%02x%02x",
                         d[off], d[off + 1], d[off + 2], d[off + 3]);
                off += 4;
            }
            if (flag_has_sel(flag)) {
                snprintf(selhex, sizeof selhex, "%02x", d[off++]);
            }

            int wrote = snprintf(out + len, cap - len,
                                 "%d %zu %d %s %s %s\n",
                                 mask, assign, (int)flag, v0hex, v1hex, selhex);
            if (wrote < 0 || (size_t)wrote >= cap - len) {
                fprintf(stderr, "output buffer overflow\n");
                return 1;
            }
            len += (size_t)wrote;
            tvdb__sw_destroy(&sw);
        }
        if (fwrite(out, 1, len, stdout) != len) {
            fprintf(stderr, "stdout write failed\n");
            return 1;
        }
        free(out);
    }

    tvdb__nodemask_destroy(&value_mask);
    return 0;
}
