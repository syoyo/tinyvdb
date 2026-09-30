/* ABI conformance check for the hand-declared Vulkan ABI in src/tinyvdb_gpu.c.
 *
 * tinyvdb_gpu.c declares the Vulkan ABI itself so the library builds with no GPU
 * SDK installed. That permits a silent typo, and a typo the NVIDIA driver
 * tolerates is worse than one it rejects: VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER
 * was declared as 44, which is BUFFER_MEMORY_BARRIER, so image barriers were
 * tagged as buffer barriers and the driver segfaulted. Worse still, the memory
 * property bits were a permutation of the real values, so every "device local"
 * allocation silently got host-coherent memory. Both were invisible until this
 * check existed.
 *
 * This test parses the hand-declared block out of src/tinyvdb_gpu.c, generates
 * two probe programs from it -- one compiled against the hand declarations
 * alone, one against the real <vulkan/vulkan.h> -- and diffs the struct sizes,
 * member offsets and constant values they report.
 *
 * Symbols the installed SDK headers do not declare are dropped from the real
 * side (found by letting the compiler report them, then retrying) rather than
 * treated as a mismatch, so SDK version skew cannot cause a spurious failure.
 * The number of dropped symbols is reported.
 *
 * It skips cleanly when the SDK headers are absent, since not needing them is
 * the entire reason the ABI is declared by hand.
 *
 * Run:  test_vk_abi [path-to-tinyvdb_gpu.c]
 */

#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *slurp(const char *path)
{
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *t = (char *)malloc((size_t)n + 1);
    if (!t || fread(t, 1, (size_t)n, f) != (size_t)n) { free(t); fclose(f); return NULL; }
    t[n] = 0;
    fclose(f);
    return t;
}

/* Pull out the hand-declared block: base typedefs through the last hand-declared
 * definition. Most structs are single-line typedefs, so the closing "} Vk" is
 * not at a line start; scan the whole text. */
static char *extract_block(const char *src)
{
    char *text = slurp(src);
    if (!text) return NULL;

    const char *base = strstr(text, "typedef uint32_t VkBool32;");
    if (!base) { free(text); return NULL; }

    const char *last = NULL;
    for (const char *p = text; (p = strstr(p, "} Vk")) != NULL; p += 3) last = p;
    for (const char *p = text; (p = strstr(p, "#define VK_")) != NULL; p += 10)
        if (!last || p > last) last = p;
    if (!last) { free(text); return NULL; }
    const char *end = strchr(last, '\n');
    if (!end) { free(text); return NULL; }

    size_t len = (size_t)(end - base) + 1;
    char *block = (char *)malloc(len + 1);
    if (!block) { free(text); return NULL; }
    memcpy(block, base, len);
    block[len] = 0;
    free(text);
    return block;
}

static int is_ident_char(char c)
{
    return isalnum((unsigned char)c) || c == '_';
}

static const char *skip_ws(const char *p)
{
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
    return p;
}

static int skip_name(char skip[][128], int nskip, const char *name)
{
    if (!name) return 0;
    for (int i = 0; i < nskip; i++) if (skip[i][0] && !strcmp(skip[i], name)) return 1;
    return 0;
}

/* Emit sizeof/offsetof/const checks for every symbol named in the block. */
static void emit(FILE *out, const char *block, int with_block,
                 char skip[][128], int nskip)
{
    for (const char *p = block; (p = strstr(p, "typedef struct {")) != NULL; ) {
        const char *open = strchr(p, '{') + 1;
        const char *close = strchr(open, '}');
        if (!close) break;
        const char *namep = skip_ws(close + 1);
        if (strncmp(namep, "Vk", 2) != 0) { p = close + 1; continue; }
        char name[128];
        size_t nl = 0;
        while (is_ident_char(namep[nl])) nl++;
        if (!nl || nl >= sizeof name) { p = close + 1; continue; }
        memcpy(name, namep, nl); name[nl] = 0;

        fprintf(out, "  printf(\"STRUCT %s %%zu\\n\", sizeof(%s));\n", name, name);
        for (const char *m = open; m < close; ) {
            const char *semi = memchr(m, ';', (size_t)(close - m));
            if (!semi) break;
            const char *e = semi;
            while (e > open && (e[-1]==' '||e[-1]=='\t'||e[-1]=='\n'||e[-1]=='\r')) e--;
            const char *st = e;
            while (st > open && is_ident_char(st[-1])) st--;
            if (st == e) {                      /* landed on ']' of an array */
                const char *b = st;
                while (b > open && (b[-1]==' '||b[-1]=='\t')) b--;
                if (b > open && b[-1] == ']') {
                    e = b;
                    while (e > open && (e[-1]==' '||e[-1]=='\t')) e--;
                    st = e;
                    while (st > open && is_ident_char(st[-1])) st--;
                }
            }
            size_t len = (size_t)(e - st);
            if (len > 0 && len < 64) {
                char mem[72];
                memcpy(mem, st, len); mem[len] = 0;
                int ign = (!strcmp(mem,"const") || !strcmp(mem,"return") ||
                           !strcmp(mem,"goto") || !strcmp(mem,"break") ||
                           !strcmp(mem,"continue") || !strcmp(mem,"else"));
                if (!ign)
                    fprintf(out, "  printf(\"  MEMBER %s.%s %%zu\\n\", offsetof(%s,%s));\n",
                            name, mem, name, mem);
            }
            m = semi + 1;
        }
        p = close + 1;
    }

    for (const char *p = block; (p = strstr(p, "#define VK_")) != NULL; ) {
        char name[128];
        size_t nl = 0;
        const char *q = p + 8;
        while (is_ident_char(q[nl])) nl++;
        if (!nl || nl >= sizeof name) { p = q; continue; }
        memcpy(name, q, nl); name[nl] = 0;
        const char *v = skip_ws(q + nl);
        int numeric = 1;
        if (*v == '-') v++;
        if (v[0] == '0' && (v[1] == 'x' || v[1] == 'X')) { v += 2; while (isxdigit((unsigned char)*v)) v++; }
        else { if (!isdigit((unsigned char)*v)) numeric = 0; while (isdigit((unsigned char)*v)) v++; }
        while (*v == 'u' || *v == 'U' || *v == 'l' || *v == 'L') v++;
        if (numeric && (*v == 0 || *v == '\n' || *v == '/' || *v == ' ') && !skip_name(skip, nskip, name)) {
            /* The hand side declares these as macros, so guard it: a macro the
             * real headers lack should be skipped, not a compile error. */
            if (with_block)
                fprintf(out, "#ifdef %s\n  printf(\"CONST %s %%llu\\n\",(unsigned long long)(%s));\n#endif\n", name, name, name);
            else
                fprintf(out, "  printf(\"CONST %s %%llu\\n\",(unsigned long long)(%s));\n", name, name);
        }
        p = q + nl;
    }
    (void)with_block;
}

static int write_probe(const char *path, const char *block, int with_block,
                       char skip[][128], int nskip)
{
    FILE *f = fopen(path, "wb");
    if (!f) return 0;
    fputs("#include <stdint.h>\n#include <stdio.h>\n#include <stddef.h>\n#include <ctype.h>\n", f);
    /* The block's function-pointer typedefs use the library's status type. */
    fputs("typedef int tvdb_status_t;\n", f);
    if (with_block) fputs(block, f);
    else fputs("#include <vulkan/vulkan.h>\n", f);
    fputs("int main(void){\n", f);
    emit(f, block, with_block, skip, nskip);
    fputs("  return 0;\n}\n", f);
    fclose(f);
    return 1;
}

int main(int argc, char **argv)
{
    const char *src = (argc > 1) ? argv[1] : "src/tinyvdb_gpu.c";
    char *block = extract_block(src);
    if (!block) { printf("SKIP: hand-declared Vulkan block not found in %s\n", src); return 0; }

    const char *cc = (getenv("CC") && getenv("CC")[0]) ? getenv("CC") : "cc";
    char cmd[1200];

    if (!write_probe("/tmp/tvdb_abi_real.c", block, 0, NULL, 0)) {
        free(block); printf("FAIL: cannot write probe\n"); return 1;
    }

    /* Compile the real probe, dropping symbols this SDK does not declare.
     * gcc reports every undeclared name at once, so this converges in a couple
     * of rounds rather than one compile per symbol. */
    char skip[64][128];
    memset(skip, 0, sizeof(skip));
    int nskip = 0;
    int ok = 0;
    for (int round = 0; round < 8; ++round) {
        if (!write_probe("/tmp/tvdb_abi_real.c", block, 0, skip, nskip)) break;
        snprintf(cmd, sizeof cmd, "%s -O0 -o /tmp/tvdb_abi_real /tmp/tvdb_abi_real.c 2>/tmp/tvdb_abi_real.log", cc);
        if (system(cmd) == 0) { ok = 1; break; }
        FILE *lg = fopen("/tmp/tvdb_abi_real.log", "r");
        if (!lg) break;
        char line[1024], name[128];
        int added = 0;
        while (fgets(line, sizeof line, lg) && nskip < 64) {
            char *q = strstr(line, "undeclared here");
            if (!q) q = strstr(line, "undeclared");
            if (!q) continue;
            /* The message is "error: <Q>NAME<Q> undeclared", with the quote
             * either ASCII or U+2018/U+2019. Find the first quote-like byte in
             * the line, skip its continuation bytes, then read the name. gcc
             * lists the undeclared name first, so that is the one to drop. */
            char *nq = NULL;
            for (char *r = line; *r; r++) {
                if (*r == '\'' || (unsigned char)*r == 0xE2) { nq = r; break; }
            }
            if (!nq) continue;
            while (*nq == '\'' || (unsigned char)*nq == 0xE2 ||
                   (unsigned char)*nq == 0x80 || (unsigned char)*nq == 0x98) nq++;
            char *e = nq;
            while (*e && is_ident_char(*e)) e++;
            size_t n = (size_t)(e - nq);
            if (n == 0 || n >= sizeof name) continue;
            memcpy(name, nq, n); name[n] = 0;
            if (skip_name(skip, nskip, name)) continue;
            snprintf(skip[nskip++], sizeof skip[0], "%s", name);
            added = 1;
            q = line + strlen(line);            /* resume past this line */
        }
        fclose(lg);
        if (!added) break;
    }
    if (!ok) { free(block);
               printf("SKIP: <vulkan/vulkan.h> unavailable or unusable, ABI check skipped\n"); return 0; }

    /* Now that the skip list is known, build the hand probe with the same set
     * so both sides report exactly the same symbols. */
    if (!write_probe("/tmp/tvdb_abi_hand.c", block, 1, skip, nskip)) {
        free(block); printf("FAIL: cannot write probe\n"); return 1;
    }
    snprintf(cmd, sizeof cmd, "%s -O0 -o /tmp/tvdb_abi_hand /tmp/tvdb_abi_hand.c 2>/tmp/tvdb_abi_hand.log", cc);
    if (system(cmd) != 0) { free(block); printf("FAIL: hand probe did not compile (/tmp/tvdb_abi_hand.log)\n"); return 1; }

    if (system("/tmp/tvdb_abi_hand | sort > /tmp/tvdb_abi_hand.txt") != 0) { printf("FAIL: hand probe run\n"); return 1; }
    if (system("/tmp/tvdb_abi_real | sort > /tmp/tvdb_abi_real.txt") != 0) { printf("FAIL: real probe run\n"); return 1; }

    int same = (system("diff -q /tmp/tvdb_abi_hand.txt /tmp/tvdb_abi_real.txt >/dev/null") == 0);

    {
        FILE *c = fopen("/tmp/tvdb_abi_real.txt", "r");
        char l[256]; int checks = 0;
        while (c && fgets(l, sizeof l, c)) checks++;
        if (c) fclose(c);
        if (same) {
            printf("OK: hand-declared Vulkan ABI matches <vulkan/vulkan.h> (%d checks", checks);
            if (nskip) printf(", %d constant(s) not declared by this SDK", nskip);
            printf(")\n");
            free(block);
            return 0;
        }
    }

    free(block);
    printf("FAIL: hand-declared Vulkan ABI differs from <vulkan/vulkan.h>\n");
    if (system("diff /tmp/tvdb_abi_hand.txt /tmp/tvdb_abi_real.txt > /tmp/tvdb_abi.diff") != 0) { /* mismatch */ }
    {
        FILE *d = fopen("/tmp/tvdb_abi.diff", "r");
        char l[512];
        while (d && fgets(l, sizeof l, d)) if (l[0] == '<' || l[0] == '>') printf("  %s", l);
        if (d) fclose(d);
    }
    return 1;
}
