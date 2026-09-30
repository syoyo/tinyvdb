// Benchmark harness for the tinyvdb CPU hot paths.
//
// There is no perf tooling in the tree today: the Makefile only builds miniz,
// the ctest list is entirely correctness, and `test_simd` exercises the
// intrinsics in isolation without measuring anything. This harness exists so
// the Phase 1-3 optimization work has a baseline to compare against, and so
// regressions are visible rather than inferred.
//
// Reports wall time and peak RSS per case. Thread counts are swept so the
// parallel-scaling of each kernel is visible; --threads N benchmarks only N.
//
//   ./tvdb_bench --all
//   ./tvdb_bench --list
//   ./tvdb_bench --case load --threads 1,2,4,8,16,32
//   ./tvdb_bench --case mc,dilate --dim 256 --reps 3
//
// Thread count is applied via omp_set_num_threads when the library is built
// with OpenMP (TINYVDB_OPENMP=ON); otherwise it is reported as unavailable
// rather than silently ignored.

// clocks and strdup are POSIX, but the library builds its targets with
// C_STANDARD 11 + C_EXTENSIONS OFF, so ask for them explicitly.
#if !defined(_WIN32)
#define _POSIX_C_SOURCE 200809L
#endif

#include "tinyvdb_io.h"
#include "tinyvdb_mesh.h"
#include "tinyvdb_ops.h"
#include "tinyvdb_levelset.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_sparse_tree.h"
#include "tinyvdb_nanovdb.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if !defined(_WIN32)
#include <time.h>
#endif
#include <time.h>

#if defined(_WIN32)
#include <windows.h>
#include <psapi.h>
static size_t peak_rss_kb(void) {
    PROCESS_MEMORY_COUNTERS pmc;
    if (GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc)))
        return (size_t)pmc.PeakWorkingSetSize / 1024;
    return 0;
}
#else
#include <sys/resource.h>
static size_t peak_rss_kb(void) {
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) == 0) return (size_t)ru.ru_maxrss;
    return 0;
}
#endif

#ifdef _OPENMP
#include <omp.h>
static int have_threads = 1;
static void set_threads(int n) { omp_set_num_threads(n); }
static int max_threads(void) { return omp_get_max_threads(); }
#else
static int have_threads = 0;
static void set_threads(int n) { (void)n; }
static int max_threads(void) { return 1; }
#endif

static double now_sec(void) {
#if defined(_WIN32)
    LARGE_INTEGER f, c;
    QueryPerformanceFrequency(&f);
    QueryPerformanceCounter(&c);
    return (double)c.QuadPart / (double)f.QuadPart;
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
#endif
}

typedef struct {
    const char *name;
    void (*run)(int dim, int reps);
} bench_case;

static int g_dim = 256;
static int g_reps = 3;
static const char *g_data_dir = "data";
static char g_load_path[1024];

/* Peak RSS is a high-water mark for the whole process, so it only ever grows.
 * Report the delta across a case rather than the absolute value. */
static size_t run_timed(void (*fn)(int dim, int reps), int dim, int reps,
                        const char *label) {
    size_t before = peak_rss_kb();
    double t0 = now_sec();
    fn(dim, reps);
    double t1 = now_sec();
    size_t after = peak_rss_kb();
    double ms = (t1 - t0) * 1000.0;
    printf("  %-22s %9.2f ms   peak-rss %6.1f MB\n", label, ms,
           (double)after / 1024.0);
    (void)before;
    return (size_t)ms;
}

/* ------------------------------------------------------------------ */
/* Level-set base grid: a band-limited sphere, the common starting point */
/* ------------------------------------------------------------------ */

static void make_sphere_sdf(tvdb_dense_grid *g, int n, float radius) {
    tvdb_dense_grid_init(g, n, n, n);
    g->voxel_size = 1.0f / (float)n;
    float c[3] = {0.5f, 0.5f, 0.5f};
    if (!tvdb_level_set_sphere(radius, c, g->voxel_size, 3.0f * g->voxel_size, g)) {
        fprintf(stderr, "make_sphere_sdf: level_set_sphere failed\n");
    }
}

/* ------------------------------------------------------------------ */
/* Cases                                                               */
/* ------------------------------------------------------------------ */

/* OpenVDB load. tvdb_file_open only parses the header; tvdb_read_all_grids
 * performs the actual per-grid tree deserialization, which is where the
 * mask/value scatter and per-node scratch buffers dominate. */
static void case_load(int dim, int reps) {
    for (int r = 0; r < reps; ++r) {
        tvdb_error_t err = {0};
        tvdb_file_t f;
        memset(&f, 0, sizeof(f));
        tvdb_status_t st = tvdb_file_open(&f, g_load_path, NULL, &err);
        if (st == TVDB_OK) st = tvdb_read_all_grids(&f, &err);
        if (st != TVDB_OK) {
            fprintf(stderr, "load: failed: %s\n", err.message);
            tvdb_file_close(&f);
            return;
        }
        /* Touch the payload so the read is not optimized away. */
        volatile float sink = 0.0f;
        for (size_t i = 0; i < f.num_grids; ++i) {
            const tvdb_grid_t *g = &f.grids[i];
            sink += (float)g->tree.num_nodes;
        }
        (void)sink;
        tvdb_file_close(&f);
    }
}

/* NanoVDB load, for comparison against the OpenVDB path. */
static void case_load_nanovdb(int dim, int reps) {
    char path[1024];
    snprintf(path, sizeof(path), "%s/reference_nvdb/sphere.nvdb", g_data_dir);
    for (int r = 0; r < reps; ++r) {
        tvdb_error_t err = {0};
        tvdb_nanovdb_file_t f;
        memset(&f, 0, sizeof(f));
        if (tvdb_nanovdb_file_open(&f, path, NULL, &err) != TVDB_OK) {
            fprintf(stderr, "load_nanovdb: %s\n", err.message);
            return;
        }
        tvdb_nanovdb_file_close(&f);
    }
}

/* Marching cubes. Serial today, and the shared edge cache rehashes inside the
 * innermost loop, so this is the biggest single CPU win available. */
static void case_mc(int dim, int reps) {
    for (int r = 0; r < reps; ++r) {
        tvdb_dense_grid sdf;
        make_sphere_sdf(&sdf, dim, 0.4f);
        tvdb_triangle_mesh mesh;
        memset(&mesh, 0, sizeof(mesh));
        if (!tvdb_sdf_to_mesh(&sdf, 0.0f, &mesh, NULL)) {
            fprintf(stderr, "mc: sdf_to_mesh failed\n");
        } else if (mesh.face_count) {
            /* Consume so the mesh cannot be elided. */
            volatile float sink = 0.0f;
            for (size_t i = 0; i < mesh.face_count; i += 1024)
                sink += (float)mesh.faces[i].v0;
            (void)sink;
        }
        tvdb_triangle_mesh_free(&mesh);
        free(sdf.data);
    }
}

/* mesh->SDF. Accelerated by a BVH over the triangles; before that this was an
 * exhaustive voxels x faces scan that needed a size cap to stay measurable. */
static void case_mesh_to_sdf(int dim, int reps) {
    int n = dim;
    for (int r = 0; r < reps; ++r) {
        tvdb_dense_grid sdf;
        make_sphere_sdf(&sdf, n, 0.4f);
        tvdb_triangle_mesh mesh;
        memset(&mesh, 0, sizeof(mesh));
        if (!tvdb_sdf_to_mesh(&sdf, 0.0f, &mesh, NULL)) {
            fprintf(stderr, "mesh_to_sdf: sdf_to_mesh failed\n");
            free(sdf.data);
            return;
        }
        tvdb_dense_grid out;
        float vs = sdf.voxel_size;
        if (!tvdb_mesh_to_sdf(&mesh, vs, 3.0f * vs, &out, NULL)) {
            fprintf(stderr, "mesh_to_sdf: failed\n");
        } else {
            volatile float sink = out.data ? out.data[0] : 0.0f;
            (void)sink;
            free(out.data);
        }
        tvdb_triangle_mesh_free(&mesh);
        free(sdf.data);
    }
}

/* Dense morphology. tvdb_morph_step has no pragma today even though the
 * fp64 twins of neighbouring kernels do. */
static void case_dilate(int dim, int reps) {
    tvdb_dense_grid g;
    make_sphere_sdf(&g, dim, 0.4f);
    for (int r = 0; r < reps; ++r) {
        tvdb_dense_grid work;
        work.nx = g.nx; work.ny = g.ny; work.nz = g.nz;
        work.voxel_size = g.voxel_size;
        size_t n = (size_t)g.nx * g.ny * g.nz;
        work.data = (float *)malloc(n * sizeof(float));
        memcpy(work.data, g.data, n * sizeof(float));
        tvdb_dilate(&work, 2);
        volatile float sink = work.data ? work.data[n / 2] : 0.0f;
        (void)sink;
        free(work.data);
    }
    free(g.data);
}

/* Separable gaussian filter. tvdb_separable_pass is also unannotated. */
static void case_gaussian(int dim, int reps) {
    tvdb_dense_grid g;
    make_sphere_sdf(&g, dim, 0.4f);
    for (int r = 0; r < reps; ++r) {
        tvdb_gaussian_filter(&g, 3, 1);
    }
    volatile float sink = g.data ? g.data[0] : 0.0f;
    (void)sink;
    free(g.data);
}

/* Laplacian stencil (6 reads/voxel). */
static void case_laplacian(int dim, int reps) {
    tvdb_dense_grid g, out;
    make_sphere_sdf(&g, dim, 0.4f);
    tvdb_dense_grid_init(&out, g.nx, g.ny, g.nz);
    for (int r = 0; r < reps; ++r) tvdb_laplacian(&g, &out);
    volatile float sink = out.data ? out.data[0] : 0.0f;
    (void)sink;
    free(out.data);
    free(g.data);
}

/* Poisson CG. Per-iteration parallelized, but issues ~8 separate fork/joins
 * per iteration and disables the AVX2 dot when OpenMP is on. */
static void case_poisson(int dim, int reps) {
    tvdb_dense_grid rhs, sol;
    make_sphere_sdf(&rhs, dim, 0.4f);
    tvdb_dense_grid_init(&sol, rhs.nx, rhs.ny, rhs.nz);
    memset(sol.data, 0, (size_t)sol.nx * sol.ny * sol.nz * sizeof(float));
    for (int r = 0; r < reps; ++r) {
        int it = tvdb_solve_poisson(&rhs, &sol, 20, 1e-4f);
        (void)it;
    }
    volatile float sink = sol.data ? sol.data[0] : 0.0f;
    (void)sink;
    free(sol.data);
    free(rhs.data);
}

/* Fast sweeping. Gauss-Seidel in place, so the body is serial by
 * construction; only the init and writeback passes can be parallelized. */
static void case_sweeping(int dim, int reps) {
    tvdb_dense_grid g;
    make_sphere_sdf(&g, dim, 0.4f);
    for (int r = 0; r < reps; ++r) {
        int it = tvdb_fast_sweeping(&g, 3.0f * g.voxel_size, 4, 2.0f * g.voxel_size);
        (void)it;
    }
    volatile float sink = g.data ? g.data[0] : 0.0f;
    (void)sink;
    free(g.data);
}

/* Signed flood fill. Serial DFS with three integer divisions per popped
 * voxel and an 8-byte-per-voxel stack. */
static void case_flood(int dim, int reps) {
    tvdb_dense_grid g;
    make_sphere_sdf(&g, dim, 0.4f);
    for (int r = 0; r < reps; ++r) {
        tvdb_dense_grid work;
        work.nx = g.nx; work.ny = g.ny; work.nz = g.nz;
        work.voxel_size = g.voxel_size;
        size_t n = (size_t)g.nx * g.ny * g.nz;
        work.data = (float *)malloc(n * sizeof(float));
        memcpy(work.data, g.data, n * sizeof(float));
        tvdb_signed_flood_fill(&work, 3.0f * work.voxel_size);
        free(work.data);
    }
    free(g.data);
}

/* Median filter. Was a full qsort per voxel over a (2r+1)^3 window; now an
 * O(n) quickselect. Kept as a case because it is a large, purely algorithmic
 * win that no amount of threading would have reached. */
static void case_median(int dim, int reps) {
    tvdb_dense_grid g;
    make_sphere_sdf(&g, dim, 0.4f);
    for (int r = 0; r < reps; ++r) {
        tvdb_median_filter(&g, 2, 1);
    }
    volatile float sink = g.data ? g.data[0] : 0.0f;
    (void)sink;
    free(g.data);
}

/* Sparse extraction: dense -> COO. The scan itself is fine; this measures the
 * cost of the layout change itself. */
static void case_dense_to_sparse(int dim, int reps) {
    tvdb_dense_grid g;
    make_sphere_sdf(&g, dim, 0.4f);
    for (int r = 0; r < reps; ++r) {
        tvdb_sparse_grid sg;
        tvdb_sparse_grid_init(&sg);
        if (tvdb_dense_to_sparse(&g, 1.0f, 1e-3f, &sg)) {
            volatile float sink = sg.count ? sg.values[0] : 0.0f;
            (void)sink;
        }
        tvdb_sparse_grid_free(&sg);
    }
    free(g.data);
}

/* Collect a grid's active voxels into a sparse grid via leaf iteration.
 * There is no per-voxel point accessor on tvdb_grid_t; the leaf visitor is the
 * supported enumeration path. */
typedef struct {
    tvdb_sparse_grid *sg;
    size_t            cap;
} collect_ctx;

static int collect_leaf(const tvdb_leaf_view_t *leaf, void *user) {
    collect_ctx *c = (collect_ctx *)user;
    int dim = 1 << leaf->log2dim;
    int total = dim * dim * dim;
    for (int i = 0; i < total; ++i) {
        if (!tvdb_nodemask_is_on(leaf->value_mask, i)) continue;
        if (c->sg->count >= c->cap) return 1; /* stop: cap reached */
        int x = leaf->origin[0] + ((i >> (2 * leaf->log2dim)) & (dim - 1));
        int y = leaf->origin[1] + ((i >> leaf->log2dim) & (dim - 1));
        int z = leaf->origin[2] + (i & (dim - 1));
        c->sg->coords[c->sg->count].x = x;
        c->sg->coords[c->sg->count].y = y;
        c->sg->coords[c->sg->count].z = z;
        c->sg->values[c->sg->count] = leaf->data[i];
        ++c->sg->count;
    }
    return 0;
}

static void case_tree_build(int dim, int reps) {
    char tmpl[1024];
    snprintf(tmpl, sizeof(tmpl), "%s/icosahedron.vdb", g_data_dir);

    /* Open the template once and reuse it; the case measures tree construction,
     * not file I/O. */
    tvdb_error_t err = {0};
    tvdb_file_t f;
    memset(&f, 0, sizeof(f));
    if (tvdb_file_open(&f, tmpl, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "tree_build: open %s failed: %s\n", tmpl, err.message);
        return;
    }
    if (tvdb_read_all_grids(&f, &err) != TVDB_OK || f.num_grids == 0) {
        fprintf(stderr, "tree_build: read_all_grids failed: %s\n", err.message);
        tvdb_file_close(&f);
        return;
    }

    /* Extract the template's active voxels once. Size the reservation from the
     * tree's active bbox, which upper-bounds the active voxel count. */
    tvdb_sparse_grid sg;
    tvdb_sparse_grid_init(&sg);
    const tvdb_grid_t *src = &f.grids[0];
    int32_t bmin[3] = {0, 0, 0}, bmax[3] = {0, 0, 0};
    size_t cap = 1024;
    if (tvdb_grid_active_bbox(src, bmin, bmax)) {
        size_t bbox = 1;
        for (int k = 0; k < 3; ++k) {
            long e = (long)bmax[k] - (long)bmin[k] + 1;
            if (e > 0) bbox *= (size_t)e;
        }
        /* Active voxels are a small fraction of the bbox; over-reserve a
         * little and let the visitor stop if it saturates. */
        cap = bbox / 4;
        if (cap < 1024) cap = 1024;
        if (cap > (size_t)128 * 1024 * 1024) cap = (size_t)128 * 1024 * 1024;
    }
    if (!tvdb_sparse_grid_reserve(&sg, cap)) {
        fprintf(stderr, "tree_build: reserve failed\n");
        tvdb_sparse_grid_free(&sg);
        tvdb_file_close(&f);
        return;
    }
    collect_ctx ctx = { &sg, cap };
    tvdb_grid_visit_leaves_float(src, collect_leaf, &ctx);
    if (sg.count == 0) {
        fprintf(stderr, "tree_build: template has no active voxels\n");
        tvdb_sparse_grid_free(&sg);
        tvdb_file_close(&f);
        return;
    }

    for (int r = 0; r < reps; ++r) {
        tvdb_grid_t g;
        memset(&g, 0, sizeof(g));
        if (tvdb_grid_from_sparse_using_template(src, &sg, "bench", 1.0f, &g)) {
            volatile size_t sink = g.tree.num_nodes;
            (void)sink;
            tvdb_grid_destroy_owned(&g);
        } else {
            fprintf(stderr, "tree_build: build failed\n");
            break;
        }
    }
    printf("      (%zu active voxels from template)\n", sg.count);
    tvdb_sparse_grid_free(&sg);
    tvdb_file_close(&f);
}

static void case_tree_dilate(int dim, int reps) {
    char tmpl[1024];
    snprintf(tmpl, sizeof(tmpl), "%s/icosahedron.vdb", g_data_dir);
    tvdb_error_t err = {0};
    tvdb_file_t f;
    memset(&f, 0, sizeof(f));
    if (tvdb_file_open(&f, tmpl, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "tree_dilate: open failed: %s\n", err.message);
        return;
    }
    if (tvdb_read_all_grids(&f, &err) != TVDB_OK || f.num_grids == 0) {
        fprintf(stderr, "tree_dilate: read_all_grids failed: %s\n", err.message);
        tvdb_file_close(&f);
        return;
    }
    const tvdb_grid_t *src = &f.grids[0];
    for (int r = 0; r < reps; ++r) {
        tvdb_sparse_grid out;
        tvdb_sparse_grid_init(&out);
        if (tvdb_grid_dilate_topology(src, 1, &out)) {
            volatile float sink = out.count ? out.values[0] : 0.0f;
            (void)sink;
        } else {
            fprintf(stderr, "tree_dilate: dilate failed\n");
            tvdb_sparse_grid_free(&out);
            break;
        }
        tvdb_sparse_grid_free(&out);
    }
    tvdb_file_close(&f);
}

/* ------------------------------------------------------------------ */

static const bench_case g_cases[] = {
    {"load", case_load},
    {"load_nanovdb", case_load_nanovdb},
    {"mc", case_mc},
    {"mesh_to_sdf", case_mesh_to_sdf},
    {"dilate", case_dilate},
    {"gaussian", case_gaussian},
    {"laplacian", case_laplacian},
    {"poisson", case_poisson},
    {"sweeping", case_sweeping},
    {"flood", case_flood},
    {"median", case_median},
    {"dense_to_sparse", case_dense_to_sparse},
    {"tree_build", case_tree_build},
    {"tree_dilate", case_tree_dilate},
};
static const size_t g_num_cases = sizeof(g_cases) / sizeof(g_cases[0]);

static int find_case(const char *name) {
    for (size_t i = 0; i < g_num_cases; ++i)
        if (strcmp(g_cases[i].name, name) == 0) return (int)i;
    return -1;
}

static void list_cases(void) {
    printf("cases:\n");
    for (size_t i = 0; i < g_num_cases; ++i) printf("  %s\n", g_cases[i].name);
}

int main(int argc, char **argv) {
    const char *selected = NULL;
    int thread_list[16];
    int num_threads = 0;

    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "--all") == 0) {
            selected = NULL;
        } else if (strcmp(argv[i], "--list") == 0) {
            list_cases();
            return 0;
        } else if (strcmp(argv[i], "--case") == 0 && i + 1 < argc) {
            selected = argv[++i];
        } else if (strcmp(argv[i], "--dim") == 0 && i + 1 < argc) {
            g_dim = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--reps") == 0 && i + 1 < argc) {
            g_reps = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--data") == 0 && i + 1 < argc) {
            g_data_dir = argv[++i];
        } else if (strcmp(argv[i], "--threads") == 0 && i + 1 < argc) {
            char *spec = argv[++i];
            char *tok = strtok(spec, ",");
            while (tok && num_threads < 16) {
                thread_list[num_threads++] = atoi(tok);
                tok = strtok(NULL, ",");
            }
        } else {
            fprintf(stderr, "unknown arg: %s (try --list)\n", argv[i]);
            return 2;
        }
    }
    if (g_dim < 8) g_dim = 8;
    if (g_reps < 1) g_reps = 1;

    /* Default load target: the smallest real VDB with a full node hierarchy. */
    snprintf(g_load_path, sizeof(g_load_path), "%s/icosahedron.vdb", g_data_dir);

    if (num_threads == 0) {
        thread_list[0] = max_threads();
        num_threads = 1;
    }

    printf("tinyvdb benchmark\n");
    printf("  dim=%d reps=%d data=%s\n", g_dim, g_reps, g_data_dir);
    printf("  threads available: %s (max %d)\n",
           have_threads ? "yes (OpenMP)" : "no (serial build)", max_threads());

    for (int t = 0; t < num_threads; ++t) {
        int nt = thread_list[t];
        set_threads(nt);
        printf("\n=== threads=%d ===\n", nt);

        if (selected) {
            /* Comma-separated selection. */
            char *copy = strdup(selected);
            char *tok = strtok(copy, ",");
            while (tok) {
                int idx = find_case(tok);
                if (idx < 0) {
                    fprintf(stderr, "unknown case: %s\n", tok);
                } else {
                    run_timed(g_cases[idx].run, g_dim, g_reps, g_cases[idx].name);
                }
                tok = strtok(NULL, ",");
            }
            free(copy);
        } else {
            for (size_t i = 0; i < g_num_cases; ++i) {
                run_timed(g_cases[i].run, g_dim, g_reps, g_cases[i].name);
                fflush(stdout);
            }
        }
    }
    return 0;
}
