/*
 * vdbdump — Dump VDB file info using TinyVDBIO (C11 library, C++11 example).
 */
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cinttypes>

#include "tinyvdbio.h"

/* Simple RAII guard for tvdb_file_t */
struct TvdbFileGuard {
    tvdb_file_t *f;
    explicit TvdbFileGuard(tvdb_file_t *fp) : f(fp) {}
    ~TvdbFileGuard() { tvdb_file_close(f); }
};

static const char *value_type_name(tvdb_value_type_t t) {
    switch (t) {
        case TVDB_VALUE_NULL:   return "null";
        case TVDB_VALUE_BOOL:   return "bool";
        case TVDB_VALUE_INT32:  return "int32";
        case TVDB_VALUE_INT64:  return "int64";
        case TVDB_VALUE_FLOAT:  return "float";
        case TVDB_VALUE_DOUBLE: return "double";
        case TVDB_VALUE_HALF:   return "half";
        case TVDB_VALUE_VEC3I:  return "vec3i";
        case TVDB_VALUE_VEC3F:  return "vec3f";
        case TVDB_VALUE_VEC3D:  return "vec3d";
        case TVDB_VALUE_STRING: return "string";
        default:                return "?";
    }
}

static const char *transform_type_name(tvdb_transform_type_t t) {
    switch (t) {
        case TVDB_TRANSFORM_UNIFORM_SCALE:           return "UniformScale";
        case TVDB_TRANSFORM_UNIFORM_SCALE_TRANSLATE:  return "UniformScaleTranslate";
        case TVDB_TRANSFORM_SCALE:                   return "Scale";
        case TVDB_TRANSFORM_SCALE_TRANSLATE:          return "ScaleTranslate";
        case TVDB_TRANSFORM_TRANSLATION:             return "Translation";
        case TVDB_TRANSFORM_AFFINE:                  return "Affine";
        case TVDB_TRANSFORM_UNKNOWN:                 return "Unknown";
        default:                                     return "?";
    }
}

static void print_value(const tvdb_value_t *v) {
    switch (v->type) {
        case TVDB_VALUE_BOOL:   printf("%s", v->u.b ? "true" : "false"); break;
        case TVDB_VALUE_INT32:  printf("%" PRId32, v->u.i32); break;
        case TVDB_VALUE_INT64:  printf("%" PRId64, v->u.i64); break;
        case TVDB_VALUE_FLOAT:  printf("%.6g", (double)v->u.f); break;
        case TVDB_VALUE_DOUBLE: printf("%.6g", v->u.d); break;
        case TVDB_VALUE_VEC3I:
            printf("(%" PRId32 ", %" PRId32 ", %" PRId32 ")",
                   v->u.vec3i[0], v->u.vec3i[1], v->u.vec3i[2]);
            break;
        case TVDB_VALUE_VEC3F:
            printf("(%.6g, %.6g, %.6g)",
                   (double)v->u.vec3f[0], (double)v->u.vec3f[1],
                   (double)v->u.vec3f[2]);
            break;
        case TVDB_VALUE_VEC3D:
            printf("(%.6g, %.6g, %.6g)",
                   v->u.vec3d[0], v->u.vec3d[1], v->u.vec3d[2]);
            break;
        case TVDB_VALUE_STRING:
            printf("\"%s\"", v->u.s.str ? v->u.s.str : "");
            break;
        default:
            printf("(null)");
            break;
    }
}

static void count_nodes(const tvdb_tree_t *tree, size_t *n_internal,
                        size_t *n_leaf, size_t *n_active_voxels) {
    *n_internal = 0;
    *n_leaf = 0;
    *n_active_voxels = 0;
    for (size_t i = 0; i < tree->num_nodes; i++) {
        const tvdb_tree_node_t *n = &tree->nodes[i];
        switch (n->type) {
            case TVDB_NODE_INTERNAL:
                (*n_internal)++;
                break;
            case TVDB_NODE_LEAF:
                (*n_leaf)++;
                *n_active_voxels +=
                    tvdb_nodemask_count_on(&n->u.leaf.value_mask);
                break;
            default:
                break;
        }
    }
}

static const char *format_count(size_t n, char *buf, size_t bufsz) {
    if (n >= 1000000000)
        snprintf(buf, bufsz, "%.2fG", (double)n / 1e9);
    else if (n >= 1000000)
        snprintf(buf, bufsz, "%.2fM", (double)n / 1e6);
    else if (n >= 1000)
        snprintf(buf, bufsz, "%.2fK", (double)n / 1e3);
    else
        snprintf(buf, bufsz, "%zu", n);
    return buf;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr,
                "Usage: %s <input.vdb> [--verbose] [--write <out.vdb>] "
                "[--write-mmap <out.vdb>]\n", argv[0]);
        return EXIT_FAILURE;
    }

    const char *infile = argv[1];
    const char *outfile = NULL;
    int verbose = 0;
    int use_mmap_write = 0;
    uint32_t compression_flags = 0;
    for (int i = 2; i < argc; i++) {
        if (strcmp(argv[i], "--verbose") == 0 || strcmp(argv[i], "-v") == 0)
            verbose = 1;
        else if (strcmp(argv[i], "--write") == 0 && i + 1 < argc)
            outfile = argv[++i];
        else if (strcmp(argv[i], "--write-mmap") == 0 && i + 1 < argc) {
            outfile = argv[++i];
            use_mmap_write = 1;
        }
    }

    tvdb_file_t file;
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    tvdb_status_t st = tvdb_file_open(&file, infile, NULL, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Error opening %s: %s (%s)\n",
                infile, err.message, tvdb_status_string(st));
        return EXIT_FAILURE;
    }
    TvdbFileGuard guard(&file);

    /* Print header */
    printf("File: %s\n", infile);
    printf("  VDB version: %u  (lib %u.%u)\n",
           file.header.file_version,
           file.header.major_version, file.header.minor_version);
    printf("  UUID: %s\n", file.header.uuid);
    printf("  Grids: %zu\n", file.num_grids);

    if (verbose && file.file_metadata.count > 0) {
        printf("  File metadata:\n");
        for (size_t i = 0; i < file.file_metadata.count; i++) {
            const tvdb_meta_entry_t *e = &file.file_metadata.entries[i];
            printf("    %s [%s] = ", e->name, e->type_name);
            print_value(&e->value);
            printf("\n");
        }
    }

    /* Read all grids */
    st = tvdb_read_all_grids(&file, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "Error reading grids: %s (%s)\n",
                err.message, tvdb_status_string(st));
        return EXIT_FAILURE;
    }

    /* Print grid info */
    for (size_t i = 0; i < file.num_grids; i++) {
        const tvdb_grid_t *g = &file.grids[i];
        printf("\n");
        printf("Grid[%zu]: \"%s\"\n", i, g->descriptor.grid_name);
        printf("  Type: %s%s\n", g->descriptor.grid_type,
               g->descriptor.save_float_as_half ? " (half)" : "");

        if (g->descriptor.instance_parent_name &&
            g->descriptor.instance_parent_name[0] != '\0') {
            printf("  Instance of: %s\n",
                   g->descriptor.instance_parent_name);
            continue;
        }

        /* Tree stats */
        const tvdb_grid_layout_t *layout = &g->tree.layout;
        printf("  Tree: %d levels [", layout->num_levels);
        for (int lv = 0; lv < layout->num_levels; lv++) {
            if (lv > 0) printf(", ");
            const char *nt = (layout->levels[lv].node_type == TVDB_NODE_ROOT)
                                 ? "Root"
                             : (layout->levels[lv].node_type == TVDB_NODE_LEAF)
                                 ? "Leaf"
                                 : "Internal";
            printf("%s(%s, log2dim=%d)", nt,
                   value_type_name(layout->levels[lv].value_type),
                   layout->levels[lv].log2dim);
        }
        printf("]\n");

        /* Background value */
        if (g->tree.num_nodes > 0 &&
            g->tree.nodes[0].type == TVDB_NODE_ROOT) {
            printf("  Background: ");
            print_value(&g->tree.nodes[0].u.root.background);
            printf("\n");

            printf("  Root: %u tiles, %u children\n",
                   g->tree.nodes[0].u.root.num_tiles,
                   g->tree.nodes[0].u.root.num_children);
        }

        size_t n_internal, n_leaf, n_active;
        count_nodes(&g->tree, &n_internal, &n_leaf, &n_active);
        char buf[32];
        printf("  Nodes: %zu total (%zu internal, %zu leaf)\n",
               g->tree.num_nodes, n_internal, n_leaf);
        printf("  Active voxels: %s\n", format_count(n_active, buf, sizeof(buf)));

        /* Transform */
        printf("  Transform: %s\n",
               transform_type_name(g->transform.type));
        printf("    Voxel size: (%.6g, %.6g, %.6g)\n",
               g->transform.voxel_size[0],
               g->transform.voxel_size[1],
               g->transform.voxel_size[2]);
        if (g->transform.type == TVDB_TRANSFORM_UNIFORM_SCALE_TRANSLATE ||
            g->transform.type == TVDB_TRANSFORM_SCALE_TRANSLATE ||
            g->transform.type == TVDB_TRANSFORM_TRANSLATION) {
            printf("    Translation: (%.6g, %.6g, %.6g)\n",
                   g->transform.translation[0],
                   g->transform.translation[1],
                   g->transform.translation[2]);
        }

        /* Compression */
        const char *comp = "none";
        if (g->compression_flags & TVDB_COMPRESS_BLOSC)
            comp = "blosc+active_mask";
        else if (g->compression_flags & TVDB_COMPRESS_ZIP)
            comp = "zip+active_mask";
        else if (g->compression_flags & TVDB_COMPRESS_ACTIVE_MASK)
            comp = "active_mask";
        printf("  Compression: %s (0x%x)\n", comp, g->compression_flags);

        /* Grid metadata (verbose) */
        if (verbose && g->metadata.count > 0) {
            printf("  Grid metadata:\n");
            for (size_t j = 0; j < g->metadata.count; j++) {
                const tvdb_meta_entry_t *e = &g->metadata.entries[j];
                printf("    %s [%s] = ", e->name, e->type_name);
                print_value(&e->value);
                printf("\n");
            }
        }
    }

    /* Write output if requested */
    if (outfile) {
        /* Use same compression as the first grid, or BLOSC+ACTIVE_MASK */
        uint32_t comp_flags = compression_flags;
        if (comp_flags == 0 && file.num_grids > 0)
            comp_flags = file.grids[0].compression_flags;
        if (comp_flags == 0)
            comp_flags = TVDB_COMPRESS_ACTIVE_MASK;

        printf("\nWriting to %s (compression=0x%x, mmap=%s)...\n",
               outfile, comp_flags, use_mmap_write ? "on" : "off");

        st = tvdb_file_save(&file, outfile, comp_flags, use_mmap_write, &err);
        if (st != TVDB_OK) {
            fprintf(stderr, "Error writing %s: %s (%s)\n",
                    outfile, err.message, tvdb_status_string(st));
            return EXIT_FAILURE;
        }
        printf("Write OK\n");
    }

    printf("\nOK\n");
    return EXIT_SUCCESS;
}
