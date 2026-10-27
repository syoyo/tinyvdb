# Preparing a release

Versions in `CMakeLists.txt`, `pyproject.toml`, `package.json`, and
`python/tinyvdb/__init__.py` must agree. Update `CHANGELOG.md` and the version
regression test together, and record the release date before publishing.

Build Python artifacts using Python 3.11 or newer, CMake 3.26 or newer, and a
C/C++ compiler. Keep artifacts and virtual environments outside the checkout:

```sh
release_root=$(mktemp -d "${TMPDIR:-/tmp}/tinyvdb-release.XXXXXX")
python3 -m venv "$release_root/env"
"$release_root/env/bin/python" -m pip install build pytest numpy twine abi3audit
# By default, build creates the sdist, then builds the wheel from that sdist.
"$release_root/env/bin/python" -m build --outdir "$release_root/dist"
"$release_root/env/bin/python" -m pip install "$release_root"/dist/*.whl
"$release_root/env/bin/python" -m pytest python/tests -x
"$release_root/env/bin/python" -m twine check --strict "$release_root"/dist/*
"$release_root/env/bin/abi3audit" --strict --summary "$release_root"/dist/*.whl
```

On Windows, use the virtual environment's `Scripts/python.exe`. Do not set
`PYTHONPATH` to a development build when testing an installed wheel. The wheel
suite covers procedural I/O round trips, sparse tools, ownership, invalidation,
and buffer contracts without local volume downloads.

Inspect archive contents before publication. Confirm the sdist contains the new
public headers, implementations, tests, maintained fixtures, dependency source,
and licenses. It must exclude local agent state, nested worktrees, downloaded
volumes, caches, and compiled products. A default wheel contains the Python
package, two `abi3` extensions, metadata, LICENSE, and THIRD_PARTY_NOTICES.md.
It uses scalar CPU kernels; SIMD and GPU support remain source-build options.

Run the affected native build/test matrix from `AGENTS.md`; record actual GPU
devices and skipped backends. An absent optional OpenVDB reference corpus returns
CTest skip code 77. The maintained fixtures and generated analytic sphere remain
available in a clean checkout. Cross-platform wheels and examples also need CI
results for each supported target; a local Linux build establishes only Linux
coverage.

The wheel workflow builds and tests supported platform wheels and independently
checks a wheel built from the sdist with Python 3.12 headers on both
Python 3.12 and the minimum Python 3.11 runtime. Manual workflow runs build artifacts. Its
existing `v*` tag trigger publishes to PyPI, so create/push a release tag only
under explicit publication authorization, after the exact outgoing history has
passed the repository's pre-push audit. Preparation alone does not authorize a
commit, tag, push, or upload.

## npm WebAssembly package

The root `package.json` publishes only `web/build-wasm/tinyvdb.js`, its
companion `.wasm` binary, and third-party notices. The `npm-publish.yml`
workflow rebuilds the Emscripten module, runs the WebAssembly runtime checks,
checks the package contents, and stages a release on `v*` tags. It uses [npm
Trusted Publishing](https://docs.npmjs.com/trusted-publishers/) with GitHub
OIDC; do not add an npm publish token to GitHub secrets. Manual runs are
limited to `main` and require the requested version to match `package.json`.
Each staged release must be reviewed and approved by a maintainer with 2FA on
npmjs.com under the package's Staged Packages tab, or with `npm stage approve`
from the CLI.

Before the first automated publish, create the package on npm once using an
npm maintainer account. npm requires a package to exist before it can have a
Trusted Publisher. Then configure the package's trusted publisher for GitHub
Actions with owner `syoyo`, repository `tinyvdb`, workflow filename
`npm-publish.yml`, and no environment. Leave direct `npm publish` and `npm
dist-tag` permissions disabled; the workflow uses `npm stage publish`, which
is allowed by default.
Alternatively, after the package exists, configure it with [npm CLI 11.15.0 or
newer](https://docs.npmjs.com/cli/v11/commands/npm-trust/) and account-level
2FA enabled:

```sh
npm trust github tinyvdb --file npm-publish.yml --repo syoyo/tinyvdb --allow-stage-publish
```

The first seed publish consumes its name/version permanently. If you seed
version 0.9.1, the workflow must wait for the next version; to publish 0.9.1
through OIDC, seed a lower version first and then manually dispatch
`npm-publish.yml` from `main` with version `0.9.1`. Future `v*` tags stage a
release for maintainer approval.
