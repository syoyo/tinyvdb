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

  // ---- level-set generators and topology measures ------------------------
  // Expected values below were produced by the native scalar build and are
  // asserted verbatim: this is the parity guard for the expanded surface.
  const sph = tv.levelSetSphere(6, 0, 0, 0, 1.0, 3.0);
  ok(sph.nx === 19 && sph.ny === 19 && sph.nz === 19,
     'levelSetSphere is 19^3 (got ' + sph.nx + '^3)');
  approx(tv.volume(sph), 895.0, 1e-3, 'sphere volume matches native');
  approx(tv.surfaceArea(sph), 654.0, 1e-3, 'sphere area matches native');
  approx(tv.levelSetEulerCharacteristic(sph, 0), 2, 1e-9, 'sphere euler characteristic = 2');
  ok(tv.levelSetGenus(sph, 0) === 0, 'sphere genus = 0');

  const tor = tv.levelSetTorus(8, 2, 0, 0, 0, 1.0, 3.0);
  approx(tv.levelSetEulerCharacteristic(tor, 0), 0, 1e-9, 'torus euler characteristic = 0');
  ok(tv.levelSetGenus(tor, 0) === 1, 'torus genus = 1');

  ok(tv.levelSetBox(4, 4, 4, 0, 0, 0, 1.0, 3.0).size() > 0, 'levelSetBox ran');
  ok(tv.levelSetCapsule(-5, 0, 0, 5, 0, 0, 2, 1.0, 3.0).size() > 0, 'levelSetCapsule ran');
  for (const faces of [4, 6, 8, 12, 20]) {
    ok(tv.levelSetPlatonic(faces, 5, 0, 0, 0, 1.0, 3.0).size() > 0,
       'levelSetPlatonic(' + faces + ') ran');
  }
  ok(tv.sdfToFogVolume(sph, 3.0).size() === sph.size(), 'sdfToFogVolume ran');
  ok(tv.sdfInteriorMask(sph, 0).size() > 0, 'sdfInteriorMask ran');
  ok(tv.sdfEnclosedRegions(sph, 0, 6).size() > 0, 'sdfEnclosedRegions ran');
  ok(tv.levelSetRebuild(sph, 0, 1.0, 3.0, 0).size() > 0, 'levelSetRebuild ran');

  // ---- statistics and health checks (native-verified) -------------------
  const st = tv.statistics(sph);
  ok(st.count === 6859, 'statistics count = ' + st.count);
  approx(st.min, -3.0, 1e-6, 'statistics min');
  approx(st.max, 3.0, 1e-6, 'statistics max');
  approx(st.mean, 2.010472, 1e-5, 'statistics mean matches native');
  approx(st.stddev, 1.570385, 1e-5, 'statistics stddev matches native');

  const h8 = tv.histogram(sph, -3, 3, 8);
  const expectH8 = [251, 138, 230, 276, 414, 482, 582, 4486];
  ok(h8.length === 8, 'histogram length 8');
  for (let i = 0; i < 8; i++) ok(h8[i] === expectH8[i], 'histogram bin ' + i + ' = ' + expectH8[i]);

  // A clamped narrow band legitimately has |grad| well below 1 on the flat
  // plateaus, so this is 0.58 natively, not 1.0.
  const lsc = tv.checkLevelSet(sph, 3.0, 0.5);
  ok(lsc.bandCount > 0, 'checkLevelSet bandCount = ' + lsc.bandCount);
  approx(lsc.meanGradMag, 0.582266, 1e-5, 'checkLevelSet meanGradMag matches native');
  const fvc = tv.checkFogVolume(tv.sdfToFogVolume(sph, 3.0), 1e-6);
  ok(fvc.valid === true, 'checkFogVolume reports valid');

  // ---- dense operators ---------------------------------------------------
  const sphB = tv.levelSetSphere(6, 3, 0, 0, 1.0, 3.0);
  ok(tv.compMax(sph, sphB).size() === sph.size(), 'compMax ran');
  ok(tv.compMin(sph, sphB).size() === sph.size(), 'compMin ran');
  ok(tv.compSum(sph, sphB).size() === sph.size(), 'compSum ran');
  ok(tv.compMult(sph, sphB).size() === sph.size(), 'compMult ran');
  approx(tv.compMax(sph, sphB).get(9, 9, 9), -3.0, 1e-6, 'compMax centre matches native');

  const m1 = tv.levelSetSphere(6, 0, 0, 0, 1.0, 3.0);
  tv.medianFilter(m1, 1, 1);
  ok(m1.size() > 0, 'medianFilter ran');
  const m2 = tv.levelSetSphere(6, 0, 0, 0, 1.0, 3.0);
  tv.meanCurvatureFlow(m2, 0.1, 2);
  ok(m2.size() > 0, 'meanCurvatureFlow ran');
  const m3 = tv.levelSetSphere(6, 0, 0, 0, 1.0, 3.0);
  tv.signedFloodFill(m3, 3.0);
  ok(m3.size() > 0, 'signedFloodFill ran');
  const fsGrid = tv.levelSetSphere(6, 0, 0, 0, 1.0, 3.0);
  ok(tv.fastSweeping(fsGrid, 1.0, 20, 1e-4) >= 0, 'fastSweeping ran');
  approx(tv.centralDiffX(sph, 9, 9, 9), 0.0, 1.0, 'centralDiffX at sphere centre');

  // ---- vector fields and advection ---------------------------------------
  const grad = tv.gradient(sph);
  ok(grad.size() === sph.size(), 'gradient dims match input');
  const gc = grad.get(9, 9, 9);
  ok(gc.length === 3, 'DenseVecGrid.get returns 3 floats');
  approx(gc[0], 0.0, 1e-6, 'gradient x at centre matches native');
  ok(tv.divergence(grad).size() === sph.size(), 'divergence ran');
  ok(tv.curl(grad).size() === sph.size(), 'curl ran');
  ok(tv.normalizeVec(grad).size() === sph.size(), 'normalizeVec ran');
  ok(tv.magnitude(grad).size() === sph.size(), 'magnitude ran');
  ok(tv.closestPointTransform(sph).size() === sph.size(), 'closestPointTransform ran');

  const vel = new tv.DenseVecGrid(sph.nx, sph.ny, sph.nz, 1.0);
  for (let z = 0; z < sph.nz; z++)
    for (let y = 0; y < sph.ny; y++)
      for (let x = 0; x < sph.nx; x++) vel.set(x, y, z, 0.1, 0, 0);
  ok(tv.advectSemiLagrangian(sph, vel, 0.1).size() === sph.size(), 'advectSemiLagrangian ran');
  for (const scheme of [tv.ADVECT_RK1, tv.ADVECT_RK2, tv.ADVECT_RK3,
                        tv.ADVECT_RK4, tv.ADVECT_MACCORMACK, tv.ADVECT_BFECC]) {
    ok(tv.advect(sph, vel, 0.05, scheme, 0).size() === sph.size(),
       'advect scheme ' + scheme + ' ran');
  }

  // ---- ray traversal (native-verified counts) ----------------------------
  ok(tv.voxelsAlongRay(sph, -20, 0, 0, 1, 0, 0, 0, 40, true) === 19,
     'voxelsAlongRay count matches native (19)');
  ok(tv.voxelsAlongRay(sph, -20, 0, 0, 1, 0, 0, 0, 40, false).length === 19 * 3,
     'voxelsAlongRay returns 3 ints per voxel');
  ok(tv.uniformRaySamples(-20, 0, 0, 1, 0, 0, 0, 40, 10, true).length === 10,
     'uniformRaySamples returns 10 t values');
  ok(tv.segmentsAlongRay(sph, -20, 0, 0, 1, 0, 0, 0, 40, 0, 200, true) === 1,
     'segmentsAlongRay pair count matches native (1)');
  ok(tv.segmentsAlongRay(sph, -20, 0, 0, 1, 0, 0, 0, 40, 0, 200, false).length === 2,
     'segmentsAlongRay returns 2 floats per pair');

  // ---- resampling and pooling (native-verified dims) ---------------------
  const cr = tv.coarsenGrid(sph, 2);
  ok(cr.nx === 10 && cr.ny === 10 && cr.nz === 10, 'coarsenGrid(2) is 10^3, matches native');
  const rf = tv.refineGrid(sph, 2);
  ok(rf.nx === 38, 'refineGrid(2) is 38^3, matches native');
  const rs = tv.resampleGrid(sph, 0.5, 1);
  ok(rs.nx === 38, 'resampleGrid(0.5) is 38^3, matches native');
  ok(tv.maxPool(sph, 2, 2, 2).nx === 10, 'maxPool(2) is 10^3, matches native');
  ok(tv.avgPool(sph, 2, 2, 2).nx === 10, 'avgPool(2) is 10^3, matches native');
  ok(tv.clipGrid(sph, -5, -5, -5, 5, 5, 5).size() > 0, 'clipGrid ran');
  ok(tv.mergeGrids(sph, sphB, 3.0).size() > 0, 'mergeGrids ran');
  const pg = tv.levelSetSphere(6, 0, 0, 0, 1.0, 3.0);
  tv.pruneGrid(pg, 3.0, 1e-3);
  ok(pg.size() > 0, 'pruneGrid ran');

  // ---- sparse grids (native-verified counts) -----------------------------
  const sp = tv.denseToSparse(sph, 3.0, 1e-3);
  ok(sp.count === 2969, 'denseToSparse count matches native (2969)');
  ok(sp.getCoords().length === 2969 * 3, 'sparse getCoords length');
  ok(sp.getValues().length === 2969, 'sparse getValues length');
  ok(tv.activeGridCoords(sph, 3.0).count > 0, 'activeGridCoords ran');
  ok(tv.sparseToDense(sp, 3.0).size() > 0, 'sparseToDense ran');
  // Sparse CSG needs both inputs in the same frame, so derive the second from
  // the first via dilate rather than from a differently-placed dense grid.
  const spD = tv.dilateSparse(sp, 3.0, 1);
  ok(spD.count === 3863, 'dilateSparse count matches native (3863)');
  ok(tv.csgUnionSparse(sp, spD, 3.0).count === 3863, 'csgUnionSparse matches native (3863)');
  ok(tv.csgIntersectionSparse(sp, spD, 3.0).count === 3863,
     'csgIntersectionSparse matches native (3863)');
  ok(tv.csgDifferenceSparse(spD, sp, 3.0).count === 3863, 'csgDifferenceSparse matches native');
  ok(tv.erodeSparse(sp, 1).count <= sp.count, 'erodeSparse ran');
  const boxKernel = new Float32Array(27).fill(1 / 27);
  ok(tv.sparseConv3d(sp, boxKernel, 3, 3, 3, 3.0).count === 2969,
     'sparseConv3d count matches native (2969)');

  // ---- hardened mesh conversion and MC tables ----------------------------
  const mx = tv.sdfToMeshEx(sph, 0, tv.WINDING_OUTWARD);
  ok(mx.numFaces() > 0, 'sdfToMeshEx(WINDING_OUTWARD) ran, ' + mx.numFaces() + ' faces');
  ok(tv.sdfToMeshEx(sph, 0, tv.WINDING_TABLE).numFaces() > 0, 'sdfToMeshEx(WINDING_TABLE) ran');
  ok(tv.meshToSDFEx(mx, 1.0, 3.0, 0).size() > 0, 'meshToSDFEx ran');
  ok(tv.mcEdgeTable().length === 256, 'mcEdgeTable has 256 entries');
  ok(tv.mcTriTableFlat().length === 4096, 'mcTriTableFlat has 4096 entries');

  // ---- invalid input must be rejected, not silently miscomputed ----------
  // NOTE: embind does not carry the exception message across the boundary in
  // this toolchain -- JS catches a bare number. The catch still works and the
  // module stays usable, so these assert only that the call is rejected.
  const mustThrow = [
    ['coarsenGrid(factor=0)', () => tv.coarsenGrid(sph, 0)],
    ['resampleGrid(voxelSize=0)', () => tv.resampleGrid(sph, 0, 1)],
    ['histogram(range max<=min)', () => tv.histogram(sph, 1, 1, 8)],
    ['histogram(nbins=0)', () => tv.histogram(sph, -1, 1, 0)],
    ['levelSetSphere(negative radius)', () => tv.levelSetSphere(-1, 0, 0, 0, 1, 3)],
    ['levelSetSphere(voxelSize=0)', () => tv.levelSetSphere(1, 0, 0, 0, 0, 3)],
    ['compMax(mismatched shapes)', () => tv.compMax(sph, new tv.DenseGrid(4, 4, 4, 1))],
    ['csgUnionSparse(mismatched frames)',
     () => tv.csgUnionSparse(sp, tv.denseToSparse(sphB, 3, 1e-3), 3)],
  ];
  for (const [label, fn] of mustThrow) {
    let threw = false;
    try { fn(); } catch (e) { threw = true; }
    ok(threw, label + ' is rejected');
  }
  // Still usable after all those throws.
  approx(tv.volume(tv.levelSetSphere(6, 0, 0, 0, 1.0, 3.0)), 895.0, 1e-3,
        'module still correct after rejections');

  // ---- demo page: the JS it calls must exist and stay correct -----------
  // Guards demo.html against silently rendering nothing. It previously used
  // `grid.voxel_size` (a C field name) instead of the bound `voxelSize`
  // property, so hwWorld was NaN and every pixel came out black.
  const demo = fs.readFileSync(path.join(WEB_DIR, 'demo.html'), 'utf8');
  ok(!/\.voxel_size\b/.test(demo), 'demo.html uses voxelSize, not the C field voxel_size');
  const demoCalls = ['levelSetSphere', 'levelSetBox', 'levelSetTorus', 'levelSetCapsule',
                     'levelSetPlatonic', 'sdfToMeshEx', 'statistics', 'checkLevelSet',
                     'levelSetEulerCharacteristic', 'levelSetGenus', 'segmentsAlongRay'];
  for (const fn of demoCalls) {
    ok(new RegExp('tv\\.' + fn + '\\b').test(demo), 'demo.html calls tv.' + fn);
    ok(typeof tv[fn] === 'function', 'tv.' + fn + ' is actually bound');
  }
  ok(/WINDING_OUTWARD/.test(demo) && tv.WINDING_OUTWARD === 1,
     'demo.html WINDING_OUTWARD constant matches the binding');
  // The default view must show the surface, not an empty corner slice.
  ok(/id="cut"[^>]*value="50"/.test(demo), 'demo clip slider defaults to the middle slice');
  const demoGrid = tv.levelSetSphere(6, 0, 0, 0, 20.0 / 64, 3.0);
  const zMid = Math.floor(demoGrid.nz * 0.5);
  const hwWorld = 3.0 * demoGrid.voxelSize;
  let inside = 0;
  for (let y = 0; y < demoGrid.nz; y++)
    for (let x = 0; x < demoGrid.nx; x++)
      if (demoGrid.get(x, y, zMid) < 0) inside++;
  ok(inside > 0, 'default demo slice contains interior voxels (' + inside + ')');

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