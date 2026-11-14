/* Differential harness: tvdb__godunov_solve (C, double twin) over seeded
 * pseudo-random sorted triples, printed for comparison against the Lean
 * `Vdb.Godunov` Float twin (lean/Vdb/GodunovCheck.lean).
 *
 * Both sides use the same LCG (Numerical Recipes) and the same draw ->
 * value mapping, so case i is identical on both sides. Values are drawn as
 * u = next() % 20000, mapped to u / 10000.0 in [0, 2), sorted
 * ascending; h is drawn as ((next() % 40000) + 5000) / 10000.0 in
 * [0.5, 4.5). The triple includes a == b == c and near-equal cases.
 *
 * Output lines: "i a b c h out" with %.17e formatting. Python parses both
 * files and checks |a-b| <= max(1e-12, 1e-12 * max(|a|, |b|)).
 *
 * Build: cc -O2 -o godunov_c godunov_c.c
 */
#include <stdint.h>
#include <math.h>
#include <stdio.h>

/* Double-precision twin of tvdb__godunov_solve (src/tinyvdb_ops.c), branch
 * by branch: 1D, then 2D, then 3D. */
static double godunov_d(double a, double b, double c, double h) {
    double x = a + h;
    if (x <= b) return x;
    double ab = a + b;
    double disc = 2.0 * h * h - (a - b) * (a - b);
    if (disc < 0.0) return x;
    x = 0.5 * (ab + sqrt(disc));
    if (x <= c) return x;
    double abc = a + b + c;
    double sumsq = a * a + b * b + c * c;
    double disc3 = abc * abc - 3.0 * (sumsq - h * h);
    if (disc3 < 0.0) return x;
    x = (abc + sqrt(disc3)) / 3.0;
    return x;
}

static uint64_t g_state;
static uint64_t next_rand(void) {
    g_state = g_state * 6364136223846793005ULL + 1442695040888963407ULL;
    return g_state >> 33;
}

int main(void) {
    enum { N = 200000 };
    g_state = 0x9e3779b97f4a7c15ULL;
    for (int i = 0; i < N; ++i) {
        double v[3];
        for (int k = 0; k < 3; ++k) {
            uint64_t u = next_rand() % 20000;
            v[k] = (double)u / 10000.0;
        }
        /* Sort ascending (insertion, all values distinct in practice). */
        for (int k = 1; k < 3; ++k) {
            double t = v[k];
            int j = k - 1;
            while (j >= 0 && v[j] > t) { v[j + 1] = v[j]; --j; }
            v[j + 1] = t;
        }
        uint64_t uh = next_rand() % 40000;
        double h = (double)(uh + 5000) / 10000.0;
        double out = godunov_d(v[0], v[1], v[2], h);
        printf("%d %.17e %.17e %.17e %.17e %.17e\n", i, v[0], v[1], v[2], h, out);
    }
    return 0;
}
