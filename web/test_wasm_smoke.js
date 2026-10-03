// Runtime smoke test for the TinyVDB WASM module.
//
// This exists because the web build silently rotted: nothing in CI built it,
// so a duplicate-symbol link failure and a missing thread-pool dependency sat
// unbroken from April. A build-only check would have caught the first bug; this
// file also proves the module *runs*, which a build cannot.
//
// It also pins the two properties that are easy to break and invisible in a
// normal native build:
//
//   1. Single-threaded. web/CMakeLists.txt must keep TINYVDB_THREAD_NONE so the
//      module needs no SharedArrayBuffer and therefore no COOP/COEP
//      cross-origin isolation headers. If someone enables pthreads, the .wasm
//      starts importing thread symbols and this test fails.
//   2. Numerically identical to the native scalar build. The field below is
//      constructed in code rather than read from a .vdb so the expected values
//      are stable across platforms; they were confirmed to match the native
//      scalar and native SIMD+OpenMP builds exactly.
//
// Uses only fixtures tracked in git (data/sphere-div*.vdb). The root-level
// sphere.vdb / bunny.vdb / cube.vdb / smoke.vdb are gitignored downloads and
// are absent on CI.
//
// Usage: node web/test_wasm_smoke.js [build-dir]
// Exits 0 on success, 1 on any failure.

'use strict';

const fs = require('fs');
const path = require('path');

const WEB_DIR = __dirname;
const REPO_ROOT = path.resolve(WEB_DIR, '..');
const BUILD_DIR = process.argv[2] || path.join(WEB_DIR, 'build-wasm');

let failures = 0;
let checks = 0;

function ok(cond, msg) {
  checks++;
  if (cond) {
    console.log('ok   ' + msg);
  } else {
    failures++;
    console.error('FAIL ' + msg);
  }
}

function approx(a, b, tol, msg) {
  ok(typeof a === 'number' && isFinite(a) && Math.abs(a - b) <= tol,
     msg + ' (' + a + ', expected ' + b + ' +/- ' + tol + ')');
}

function requireFile(p, what) {
  if (!fs.existsSync(p)) {
    console.error('FAIL missing ' + what + ': ' + p);
    process.exit(1);
  }
  return p;
}

(async () => {
  const jsPath = requireFile(path.join(BUILD_DIR, 'tinyvdb.js'), 'tinyvdb.js');
  const wasmPath = requireFile(path.join(BUILD_DIR, 'tinyvdb.wasm'), 'tinyvdb.wasm');

  // ---- single-threaded guarantees, checked before we load anything --------
  const glue = fs.readFileSync(jsPath, 'utf8');
  ok(!/USE_PTHREADS/.test(glue), 'JS glue does not request USE_PTHREADS');
  ok(!/SharedArrayBuffer/.test(glue), 'JS glue does not reference SharedArrayBuffer');

  // Import names are stored as plain ASCII in the wasm binary, so a substring
  // scan catches a pthreads build without needing a wasm parser.
  const wasm = fs.readFileSync(wasmPath);
  const wasmText = wasm.toString('latin1');
  ok(!/pthread/.test(wasmText), '.wasm imports no pthread symbols');
  ok(!/thrd_/.test(wasmText), '.wasm imports no C11 threads symbols');
  ok(wasm[0] === 0x00 && wasm[1] === 0x61 && wasm[2] === 0x73 && wasm[3] === 0x6d,
     '.wasm has the \\0asm magic');

  const TinyVDB = require(jsPath);
  const tv = await TinyVDB();
  ok(!!tv && typeof tv.VDBFile === 'function', 'module instantiated and exposes VDBFile');

  // ---- reading real, git-tracked fixtures --------------------------------
  for (const rel of ['data/sphere-div1.vdb', 'data/sphere-div2.vdb']) {
    const buf = fs.readFileSync(path.join(REPO_ROOT, rel));
    const f = new tv.VDBFile();
    f.openMemoryFromArray(buf);
    ok(f.gridCount() >= 1, rel + ': gridCount = ' + f.gridCount());
    f.readGrids();
    ok(f.gridName(0).length > 0, rel + ': gridName(0) = "' + f.gridName(0) + '"');
    ok(/float/i.test(f.gridTypeName(0)), rel + ': gridTypeName(0) = ' + f.gridTypeName(0));
    ok(f.treeNodeCount(0) > 0, rel + ': treeNodeCount(0) = ' + f.treeNodeCount(0));
    const hdr = f.header();
    ok(hdr && hdr.majorVersion > 0,
       rel + ': header majorVersion = ' + (hdr && hdr.majorVersion));
    const out = f.toBytes();
    const n = out ? (out.length || out.byteLength || 0) : 0;
    ok(n > 0, rel + ': toBytes -> ' + n + ' bytes');
    f.close();
  }

  // ---- deterministic field, for native parity ----------------------------
  // Sphere of radius 6 centred in a 16^3 grid at voxel size 1. Built in code
  // (not read from disk) so the expectations below are exact and portable.
  const g = new tv.DenseGrid(16, 16, 16, 1.0);
  ok(g.size() === 16 * 16 * 16, 'DenseGrid(16^3).size = ' + g.size());
  for (let z = 0; z < 16; z++) {
    for (let y = 0; y < 16; y++) {
      for (let x = 0; x < 16; x++) {
        const dx = x - 8, dy = y - 8, dz = z - 8;
        g.set(x, y, z, Math.sqrt(dx * dx + dy * dy + dz * dz) - 6.0);
      }
    }
  }
  approx(g.get(8, 8, 8), -6.0, 1e-5, 'field value at centre');

  // ---- kernels: these are the paths that use the thread pool -------------
  approx(tv.volume(g), 895.0, 1e-3, 'volume matches native');
  approx(tv.surfaceArea(g), 654.0, 1e-3, 'surfaceArea matches native');

  const d1 = tv.dilate(g, 1);
  ok(d1 && d1.size() === g.size(), 'dilate(1) ran');
  const e1 = tv.erode(g, 1);
  ok(e1 && e1.size() === g.size(), 'erode(1) ran');
  const mo = tv.morphOpen(g, 1);
  ok(mo && mo.size() === g.size(), 'morphOpen(1) ran');
  const mc = tv.morphClose(g, 1);
  ok(mc && mc.size() === g.size(), 'morphClose(1) ran');
  ok(tv.gaussianFilter(g, 1).size() === g.size(), 'gaussianFilter(1) ran');
  ok(tv.meanFilter(g, 1).size() === g.size(), 'meanFilter(1) ran');
  ok(tv.laplacianFilter(g, 1).size() === g.size(), 'laplacianFilter(1) ran');
  ok(tv.csgUnion(g, d1).size() === g.size(), 'csgUnion ran');
  ok(tv.csgIntersection(g, d1).size() === g.size(), 'csgIntersection ran');
  ok(tv.csgDifference(g, d1).size() === g.size(), 'csgDifference ran');

  // ---- marching cubes + mesh round trip ----------------------------------
  const m = tv.sdfToMesh(g, 0.0);
  ok(m && m.numVertices() === 654, 'sdfToMesh vertex count matches native (654)');
  ok(m && m.numFaces() === 1304, 'sdfToMesh face count matches native (1304)');
  const verts = m.getVertices();
  ok(verts && verts.length === 654 * 3, 'getVertices -> ' + (verts ? verts.length : 0) + ' floats');
  // getFaces returns uint32 vertex indices, 3 per triangle -- not 9 floats.
  const faces = m.getFaces();
  ok(faces && faces.length === 1304 * 3, 'getFaces -> ' + (faces ? faces.length : 0) + ' uint32 indices');

  const back = tv.meshToSDF(m, 1.0, 3.0, 0);
  ok(back && back.size() > 0, 'meshToSDF ran');

  // Signature is (mesh, resolution, isovalue, signMethod).
  const mf = tv.makeManifold(m, 1.0, 0.0, 0);
  ok(mf && typeof mf.numFaces === 'function', 'makeManifold ran, ' +
     (mf ? mf.numFaces() : '?') + ' faces');

  console.log('');
  if (failures) {
    console.error(failures + ' of ' + checks + ' checks FAILED');
    process.exitCode = 1;
  } else {
    console.log('all ' + checks + ' wasm smoke checks passed');
  }
})().catch((e) => {
  console.error('EXCEPTION: ' + ((e && e.stack) || e));
  process.exitCode = 1;
});