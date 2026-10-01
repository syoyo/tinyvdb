# Agent guidance

This file applies throughout this repository. The pre-push policy is adapted
from the tinyusdz development repository's `AGENTS.md`, with validation specific
to tinyvdbio.

## Development and validation

The core library uses C11; C++ examples use C++11. Treat `CMakeLists.txt` as the
source of truth for build options and test registration. GPU support loads
Vulkan and CUDA at runtime, so a successful build does not establish that either
backend ran successfully.

Preserve unrelated edits and untracked files. Keep build products, local agent
state, scratch scripts, and scanner reports outside tracked source. Use fresh,
out-of-tree build directories when changing configuration. Prefer Ninja when
available. Add a regression test for a behavior fix when it can demonstrate the
failure, then run the relevant suite. Documentation-only changes require a
content review, command/link checks, and whitespace checks; they do not require
rerunning the full backend matrix.

## Pre-push procedure

Complete this procedure before publishing commits, including a force push.
An audit or fix request alone does not authorize a push. Honor an existing
explicit push authorization for its stated scope; ask only when authorization
is missing or the destination, commits, or history-rewrite scope has changed.

### 1. Establish the exact destination and commit range

Inspect the working tree, current branch, upstream, and configured remote.
Identify the destination branch explicitly if there is no upstream. Fetch the
destination's current tip before claiming the local branch is ready to push.
If the remote cannot be checked, report that limitation instead of claiming
remote readiness.

Use the fetched destination tip as the audit base, and record the proposed local
tip by commit ID. Review every commit reachable from the proposed tip that is
not reachable from the destination tip. For an existing destination:

```bash
# Set these to the resolved commit IDs, not an assumed upstream.
audit_base=<fetched-destination-tip>
audit_tip=<proposed-local-tip>
audit_range="$audit_base..$audit_tip"
git log --oneline "$audit_range"
git log --format=fuller --name-status "$audit_range"
git log --format=fuller --patch --binary "$audit_range"
git diff --check "$audit_range"
```

For a new remote branch, establish which commits will newly become public and
audit their complete history. If no trustworthy published base exists, audit
all ancestors of the proposed tip. Do not invent a base or silently use only
the latest commit. Check whether the destination tip is an ancestor of the
proposed tip; any non-fast-forward update requires explicit authorization.

Endpoint diffs are insufficient: a secret or artifact added in one outgoing
commit and deleted in another is still published. Inspect per-commit patches,
filenames, and messages, including merges and any renamed or binary content.
Recompute the range after a commit, rebase, amend, or remote-tip change.

### 2. Audit secrets and publication hygiene

Review all outgoing commits for:

- Credentials, private keys, tokens, passwords, credential-bearing URLs,
  authentication configuration, and environment files.
- Private hostnames, customer data, proprietary asset names, and personal
  absolute paths in source, documentation, filenames, and commit messages.
- Build output, caches, executables, libraries, generated shader binaries,
  temporary dumps, scanner reports, and local agent directories.
- Large or binary files, including VDB/NanoVDB volumes and captured output.
  Curated fixtures or documentation assets must be intentional, appropriately
  licensed, reasonably sized, and justified. Existing maintained fallback
  shader source is not disposable build output.

Run an available secret scanner against the same history range with redacted
output. Check the installed version's help before choosing its syntax. For
versions supporting `detect`, an example is:

```bash
gitleaks detect --source . --redact --log-opts="$audit_range"
```

For an audit of the complete ancestry, pass the proposed tip instead of the
range. Inspect commit messages manually as well. Scanners supplement manual
review; they do not prove the absence of secrets. Do not exclude documentation
or text files from review. Keep reports outside the repository and avoid
printing suspected secret values. Additional scanners must cover the intended
range; do not send suspected credentials to external verification services
without authorization.

A scanner finding or execution error blocks a clean audit until resolved.
If no scanner is available, document that fact and perform a manual review;
do not present a skipped check as a passing check. Review intentional test
strings before accepting any narrowly scoped exception.

Remove offending content from every outgoing commit that contains it, not
just the final tree. Coordinate credential rotation with the owner for an
actual exposed credential. Preserve unrelated work and obtain authorization
before rewriting published history or performing destructive cleanup. Repeat
the audit after remediation.

### 3. Validate the affected behavior

Scale checks to the changes. For core operations, sparse topology, allocation,
or GPU changes, use the following matrix. Build each configuration before
running CTest; stop on configuration, compilation, or test errors.

```bash
# Run from the repository root. mktemp keeps products outside source.
audit_build_root=$(mktemp -d "${TMPDIR:-/tmp}/tinyvdb-prepush.XXXXXX")

# Scalar CPU with sanitizers.
cmake -S . -B "$audit_build_root/scalar" -G Ninja \
  -DTINYVDB_BUILD_TESTS=ON -DTINYVDB_BUILD_EXAMPLES=OFF \
  -DTINYVDB_BUILD_VDBRENDER=OFF -DTINYVDB_BUILD_GPU=OFF \
  -DTINYVDB_SIMD=OFF -DTINYVDB_OPENMP=OFF \
  -DCMAKE_C_FLAGS="-fsanitize=address,undefined,float-cast-overflow -fno-omit-frame-pointer -g -O1" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address,undefined,float-cast-overflow"
cmake --build "$audit_build_root/scalar"
ctest --test-dir "$audit_build_root/scalar" --output-on-failure

# SIMD and OpenMP CPU paths.
cmake -S . -B "$audit_build_root/parallel" -G Ninja \
  -DTINYVDB_BUILD_TESTS=ON -DTINYVDB_BUILD_EXAMPLES=OFF \
  -DTINYVDB_BUILD_VDBRENDER=OFF -DTINYVDB_BUILD_GPU=OFF \
  -DTINYVDB_SIMD=ON -DTINYVDB_OPENMP=ON
cmake --build "$audit_build_root/parallel"
OMP_NUM_THREADS=1 ctest --test-dir "$audit_build_root/parallel" --output-on-failure
OMP_NUM_THREADS=8 ctest --test-dir "$audit_build_root/parallel" --output-on-failure

# Generated shaders: glslangValidator and xxd must be available.
cmake -S . -B "$audit_build_root/gpu" -G Ninja \
  -DTINYVDB_BUILD_TESTS=ON -DTINYVDB_BUILD_EXAMPLES=OFF \
  -DTINYVDB_BUILD_VDBRENDER=OFF -DTINYVDB_BUILD_GPU=ON
cmake --build "$audit_build_root/gpu"
ctest --test-dir "$audit_build_root/gpu" --output-on-failure

# No generated shaders: use a fresh directory and an explicitly empty path.
cmake -S . -B "$audit_build_root/fallback" -G Ninja \
  -DTINYVDB_BUILD_TESTS=ON -DTINYVDB_BUILD_EXAMPLES=OFF \
  -DTINYVDB_BUILD_VDBRENDER=OFF -DTINYVDB_BUILD_GPU=ON \
  -DTINYVDB_GLSLANG_VALIDATOR:FILEPATH=
cmake --build "$audit_build_root/fallback"
ctest --test-dir "$audit_build_root/fallback" --output-on-failure
```

Verify configuration logs actually enable the intended SIMD/OpenMP paths and
generate shaders in the GPU build. Reusing a directory with generated includes
can invalidate the fallback check. Adapt the compiler or generator to the
platform and report unavailable checks. Keep sanitizers enabled; if a specific
sanitizer runtime feature is unsupported, state the workaround and limitation.

Review operation contracts for aliasing, failure-time output preservation,
allocation failure, overflow, nonfinite input, empty grids, sparse background
and active topology, coordinate bounds, and precision where applicable.
Poisson/PDE changes also require boundary-condition and convergence checks.
GPU changes require dispatch/failure tests, shader ABI checks, fallback checks,
and comparison with CPU behavior for both Vulkan and CUDA where available.

CTest exit code 77 denotes a skipped backend test, not a pass. Record skips and
the actual device/backend used, including software Vulkan. Mock-driver tests
and NVRTC compilation do not establish CUDA device arithmetic correctness.
When device coverage is unavailable, report the limitation explicitly.

For Python, web/WASM, examples, packaging, or CI changes, additionally follow
the relevant component's build instructions and exercise the affected entry
points. Rebuild bindings before testing them. Update public documentation when
behavior or supported configurations change.

### 4. Report readiness and publish only the audited tip

Before pushing, summarize the destination remote and branch, proposed tip,
commit count and subjects, fast-forward or authorized rewrite status, audit
results, validation results, and unavailable checks. Distinguish passing,
skipped, and failed checks. Do not call unresolved findings safe to push.

Push only the reviewed refspec under the user's authorization. For an
authorized rewrite, use an explicit lease tied to the fetched destination tip;
do not use an unconditional force push. If the destination changes, reassess
the range and lease instead of overriding the change. After publication,
verify the destination tip and report relevant CI status without claiming
unobserved success. Do not delete branches or publish unrelated refs.

## Pre-push checklist

- [ ] Destination remote, branch, proposed tip, and authorization are resolved.
- [ ] Remote tip is current; exact outgoing history and update type are known.
- [ ] Every outgoing commit's patches, filenames, and messages were reviewed.
- [ ] Secrets, private data, personal paths, artifacts, and binary sizes checked.
- [ ] Secret scanner passed, or its absence and manual review are reported.
- [ ] Findings remediated across history; audit rerun after any tip change.
- [ ] Relevant builds and tests passed for the intended configurations.
- [ ] Backend skips, device coverage, and other limitations are explicit.
- [ ] Documentation reflects changed contracts; whitespace checks passed.
- [ ] Readiness summary identifies exactly what will be pushed.
- [ ] After pushing, remote tip and available CI results are verified/reported.
