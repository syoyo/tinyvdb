#!/usr/bin/env python3
"""End-to-end capstone demo exercising the new tinyvdbio op surface.

Pipeline:
  1. Build a particle-cloud SDF (multiple overlapping spheres)
  2. Compute gradient + laplacian (Phase 2)
  3. Render N synthetic depth frames around the SDF using ray-cast (Phase 6)
  4. Fuse the depth frames into a TSDF (Phase 4)
  5. Marching-cubes the TSDF and the original SDF (Phase 6 / mesh.c)
  6. Write both meshes as OBJ files

Run:
  PYTHONPATH=python python3 scripts/capstone_demo.py
"""

from __future__ import annotations

import math
import os
import struct
import sys

import tinyvdb


def make_obj(path: str, verts_bytes: bytes, faces_bytes: bytes) -> None:
    nv = len(verts_bytes) // 12  # 3 floats per vertex
    nf = len(faces_bytes) // 12  # 3 uint32 per face
    verts = struct.unpack(f"{nv * 3}f", verts_bytes)
    faces = struct.unpack(f"{nf * 3}I", faces_bytes)
    with open(path, "w") as f:
        f.write(f"# {nv} verts, {nf} faces\n")
        for i in range(nv):
            f.write(f"v {verts[3*i]} {verts[3*i+1]} {verts[3*i+2]}\n")
        for i in range(nf):
            # OBJ is 1-indexed
            f.write(f"f {faces[3*i]+1} {faces[3*i+1]+1} {faces[3*i+2]+1}\n")


def world_to_pixel(fx: float, fy: float, cx: float, cy: float,
                   x: float, y: float, z: float) -> tuple[float, float] | None:
    if z <= 0.0:
        return None
    return fx * x / z + cx, fy * y / z + cy


def render_depth_from_sdf(sdf: "tinyvdb.DenseGrid",
                          pose_wc: tuple[float, ...],
                          fx: float, fy: float, cx: float, cy: float,
                          W: int, H: int, max_depth: float = 10.0) -> bytes:
    """For each pixel, cast a ray from the camera into the world and record
    the SDF intersection depth in camera-Z. Returns a bytes buffer of W*H
    float32 depths (0 = no hit)."""
    # pose_wc is row-major 4x3 [R | t]: world = R*cam + t. Camera-Z axis in
    # world is column 3 of R, i.e. (pose_wc[2], pose_wc[6], pose_wc[10]).
    R0 = (pose_wc[0], pose_wc[1], pose_wc[2])
    R1 = (pose_wc[4], pose_wc[5], pose_wc[6])
    R2 = (pose_wc[8], pose_wc[9], pose_wc[10])
    cam_pos = (pose_wc[3], pose_wc[7], pose_wc[11])

    out = bytearray(W * H * 4)
    for v in range(H):
        for u in range(W):
            # Ray direction in camera space at pixel (u, v): (x_c, y_c, 1).
            xc = (u - cx) / fx
            yc = (v - cy) / fy
            zc = 1.0
            # Rotate to world: world_dir = R * (xc, yc, zc).
            dx = R0[0] * xc + R0[1] * yc + R0[2] * zc
            dy = R1[0] * xc + R1[1] * yc + R1[2] * zc
            dz = R2[0] * xc + R2[1] * yc + R2[2] * zc
            ln = math.sqrt(dx * dx + dy * dy + dz * dz)
            if ln < 1e-12:
                continue
            dx /= ln; dy /= ln; dz /= ln
            hit = tinyvdb.ray_cast_sdf(grid=sdf,
                                       origin=cam_pos,
                                       direction=(dx, dy, dz),
                                       max_t=max_depth * ln)
            if hit is None:
                continue
            t = hit["t"]  # world-space distance to hit
            # Camera-space Z of the hit = world-space distance projected onto
            # the camera +Z axis (R2). Since direction was normalized, and the
            # original "cam ray" is (xc, yc, 1), we have ||(xc,yc,1)|| = ln,
            # so camera-Z of hit = t / ln.
            depth = t / ln
            if depth <= 0 or depth >= max_depth:
                continue
            struct.pack_into("f", out, (v * W + u) * 4, depth)
    return bytes(out)


def main() -> int:
    out_dir = sys.argv[1] if len(sys.argv) > 1 else "/tmp/tinyvdbio_capstone"
    os.makedirs(out_dir, exist_ok=True)
    print(f"[capstone] writing artifacts to {out_dir}")

    # ---------------------------------------------------------------
    # Step 1: build SDF from a small particle cloud (3 overlapping spheres).
    # ---------------------------------------------------------------
    positions = struct.pack(
        "9f",
         0.0,  0.0, 0.0,
         0.6,  0.0, 0.0,
         0.0,  0.5, 0.0,
    )
    radii = struct.pack("3f", 0.5, 0.4, 0.3)
    sdf = tinyvdb.particles_to_sdf(
        positions=positions, radii=radii,
        voxel_size=0.05, band_width=0.4)
    print(f"[capstone] SDF shape={sdf.shape} origin={sdf.origin} vs={sdf.voxel_size:.3f}")
    print(f"[capstone] SDF volume       = {tinyvdb.volume(sdf):.4f}")
    print(f"[capstone] SDF surface area = {tinyvdb.surface_area(sdf):.4f}")

    # ---------------------------------------------------------------
    # Step 2: compute gradient + laplacian (Phase 2 ops)
    # ---------------------------------------------------------------
    grad = tinyvdb.gradient(sdf)
    lap = tinyvdb.laplacian(sdf)
    print(f"[capstone] gradient shape={grad.shape}, laplacian shape={lap.shape}")

    # ---------------------------------------------------------------
    # Step 3 + 4: render synthetic depth frames from a 360-fly-around and
    # fuse them all into a shared TSDF using the in-place multi-frame
    # binding `integrate_tsdf_into`.
    # ---------------------------------------------------------------
    W, H = 96, 96
    fx = fy = 96.0
    cx_p = cy_p = 48.0
    trunc = 0.2

    # Persistent TSDF + weight buffers (reused across frames).
    tsdf = tinyvdb.DenseGrid(nx=48, ny=48, nz=48, voxel_size=0.05,
                             ox=-1.2, oy=-1.2, oz=-1.2)
    wgt  = tinyvdb.DenseGrid(nx=48, ny=48, nz=48, voxel_size=0.05,
                             ox=-1.2, oy=-1.2, oz=-1.2)
    # Initialize TSDF to +trunc (far outside).
    for iz in range(48):
      for iy in range(48):
        for ix in range(48):
          tsdf.set((ix, iy, iz), trunc)

    n_frames = 8
    cam_radius = 3.0
    cam_height = 0.4
    valid_total = 0
    for k in range(n_frames):
        theta = 2.0 * math.pi * k / n_frames
        cx, cy, cz = (cam_radius * math.sin(theta), cam_height, cam_radius * math.cos(theta))
        # Build a world<-camera pose: camera looks at origin from (cx, cy, cz).
        # forward = -(cam_pos)/|cam_pos|; right = forward x up; up' = right x forward.
        fxv = -cx; fyv = -cy; fzv = -cz
        L = math.sqrt(fxv*fxv + fyv*fyv + fzv*fzv); fxv/=L; fyv/=L; fzv/=L
        # world up
        ux, uy, uz = 0.0, 1.0, 0.0
        # right = forward x up
        rx_ = fyv*uz - fzv*uy
        ry_ = fzv*ux - fxv*uz
        rz_ = fxv*uy - fyv*ux
        Lr = math.sqrt(rx_*rx_ + ry_*ry_ + rz_*rz_); rx_/=Lr; ry_/=Lr; rz_/=Lr
        # cam +X = right; cam +Y = -up' (image y down); cam +Z = forward (toward origin)
        # up' = right x forward
        up_x = ry_*fzv - rz_*fyv
        up_y = rz_*fxv - rx_*fzv
        up_z = rx_*fyv - ry_*fxv
        # World<-camera columns: [right | -up' | forward], translation = cam pos.
        pose = struct.pack(
            "12f",
            rx_, -up_x, fxv, cx,
            ry_, -up_y, fyv, cy,
            rz_, -up_z, fzv, cz,
        )
        pose_t = struct.unpack("12f", pose)
        depth = render_depth_from_sdf(sdf, pose_t, fx, fy, cx_p, cy_p, W, H, max_depth=8.0)
        valid = sum(1 for v in struct.unpack(f"{W*H}f", depth) if v > 0.0)
        valid_total += valid
        if valid == 0:
            continue
        tinyvdb.integrate_tsdf_into(
            tsdf=tsdf, weights=wgt, depth=depth,
            width=W, height=H, fx=fx, fy=fy, cx=cx_p, cy=cy_p,
            pose=pose, trunc=trunc, depth_min=0.1, depth_max=8.0)
    print(f"[capstone] fused {n_frames} frames; total valid pixels = {valid_total}")
    print(f"[capstone] TSDF shape={tsdf.shape}")

    # ---------------------------------------------------------------
    # Step 4b: medial-axis sphere covering of the SDF interior
    # ---------------------------------------------------------------
    spheres = tinyvdb.volume_to_spheres(grid=sdf, min_radius=0.05,
                                        max_spheres=8, overlap=0.4)
    sph_count = spheres["count"]
    print(f"[capstone] volume_to_spheres found {sph_count} interior spheres")
    if sph_count > 0:
        cs = struct.unpack(f"{sph_count*3}f", spheres["centers"])
        rs = struct.unpack(f"{sph_count}f",   spheres["radii"])
        for i in range(min(sph_count, 4)):
            print(f"           sphere {i}: c={cs[3*i:3*i+3]} r={rs[i]:.4f}")

    # ---------------------------------------------------------------
    # Step 5: marching cubes on both SDFs
    # ---------------------------------------------------------------
    # SDF -> mesh
    sdf_mesh = tinyvdb.sdf_to_mesh(sdf, isovalue=0.0)
    print(f"[capstone] SDF mesh:  {sdf_mesh.num_vertices} verts, {sdf_mesh.num_faces} faces")

    sdf_obj = os.path.join(out_dir, "sdf_mesh.obj")
    make_obj(sdf_obj, sdf_mesh.vertices_bytes, sdf_mesh.faces_bytes)
    print(f"[capstone] wrote {sdf_obj}")

    if tsdf is not None:
        tsdf_mesh = tinyvdb.sdf_to_mesh(tsdf, isovalue=0.0)
        print(f"[capstone] TSDF mesh: {tsdf_mesh.num_vertices} verts, {tsdf_mesh.num_faces} faces")
        tsdf_obj = os.path.join(out_dir, "tsdf_mesh.obj")
        make_obj(tsdf_obj, tsdf_mesh.vertices_bytes, tsdf_mesh.faces_bytes)
        print(f"[capstone] wrote {tsdf_obj}")

    print("[capstone] done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
