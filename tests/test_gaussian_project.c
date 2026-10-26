/* tvdb_gaussian_project: CPU projection of 3D Gaussian splats to 2D conics.
 * Compares the EWA 2D covariance and the radius against an independent
 * reference, checks the structural symmetry of a 90 degree turn about the view
 * axis, culling, opacity, features and argument handling. This is the only CPU
 * test that reaches the full 3x3 rotated covariance (the GPU parity test needs
 * a device). */
#include "tinyvdb_nanovdb.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(x)                                                                     \
    do {                                                                             \
        if (!(x)) {                                                                  \
            fprintf(stderr, "line %d: %s (%s)\n", __LINE__, #x, err.message);         \
            return 1;                                                                \
        }                                                                            \
    } while (0)

static const double k_eps2d = 0.3;

static void rot_from_quat(const float q[4], double R[9]) {
    const double x = q[0], y = q[1], z = q[2], w = q[3];
    R[0] = 1 - 2 * (y * y + z * z);
    R[1] = 2 * (x * y - w * z);
    R[2] = 2 * (x * z + w * y);
    R[3] = 2 * (x * y + w * z);
    R[4] = 1 - 2 * (x * x + z * z);
    R[5] = 2 * (y * z - w * x);
    R[6] = 2 * (x * z - w * y);
    R[7] = 2 * (y * z + w * x);
    R[8] = 1 - 2 * (x * x + y * y);
}
static void quat_mul(const float a[4], const float b[4], float out[4]) {
    out[0] = a[3] * b[0] + a[0] * b[3] + a[1] * b[2] - a[2] * b[1];
    out[1] = a[3] * b[1] - a[0] * b[2] + a[1] * b[3] + a[2] * b[0];
    out[2] = a[3] * b[2] + a[0] * b[1] - a[1] * b[0] + a[2] * b[3];
    out[3] = a[3] * b[3] - a[0] * b[0] - a[1] * b[1] - a[2] * b[2];
}

/* Independent reference: screen position, epsilon-regularised 2D covariance
 * and its three-sigma major axis. Returns 0 when the splat is culled. */
static int reference(const float mean[3], const float quat[4], const float scale[3],
                     const tvdb_camera_t *cam, double xy[2], double cov2d[3],
                     double *radius) {
    const double depth = mean[2];
    if (depth <= cam->near || depth >= cam->far) return 0;
    const double fx = cam->intrinsics[0], fy = cam->intrinsics[4];
    const double cx = cam->intrinsics[2], cy = cam->intrinsics[5];
    const double x = fx * mean[0] / depth + cx, y = fy * mean[1] / depth + cy;
    xy[0] = x;
    xy[1] = y;
    double R[9];
    rot_from_quat(quat, R);
    const double s2[3] = {scale[0] * scale[0], scale[1] * scale[1],
                          scale[2] * scale[2]};
    double cov[3][3];
    for (int r = 0; r < 3; ++r)
        for (int c = 0; c < 3; ++c) {
            cov[r][c] = 0;
            for (int k = 0; k < 3; ++k) cov[r][c] += R[r * 3 + k] * s2[k] * R[c * 3 + k];
        }
    /* Pinhole Jacobian at this offset (skew-free, z along the view axis). */
    const double dx = x - cx, dy = y - cy;
    const double J[2][3] = {{fx / depth, 0, -dx / depth},
                            {0, fy / depth, -dy / depth}};
    double m[2][2];
    for (int r = 0; r < 2; ++r)
        for (int c = 0; c < 2; ++c) {
            m[r][c] = 0;
            for (int a = 0; a < 3; ++a)
                for (int b = 0; b < 3; ++b) m[r][c] += J[r][a] * cov[a][b] * J[c][b];
        }
    cov2d[0] = m[0][0] + k_eps2d;
    cov2d[1] = m[0][1];
    cov2d[2] = m[1][1] + k_eps2d;
    const double mid = 0.5 * (cov2d[0] + cov2d[2]);
    *radius = 3.0 * sqrt(mid + 0.5 * sqrt((cov2d[0] - cov2d[2]) * (cov2d[0] - cov2d[2]) +
                                          4 * cov2d[1] * cov2d[1]));
    return 1;
}

static int close_to(double a, double b, double tol) { return fabs(a - b) <= tol; }

static void camera(tvdb_camera_t *cam) {
    memset(cam, 0, sizeof(*cam));
    cam->type = TVDB_CAMERA_PERSPECTIVE;
    cam->fx = cam->fy = 800.0f; /* equal focals: view-axis turns stay 2D rotations */
    cam->cx = 320.5f;
    cam->cy = 240.5f;
    cam->width = 640;
    cam->height = 480;
    cam->near = 0.05f;
    cam->far = 100.0f;
    cam->intrinsics[0] = cam->fx;
    cam->intrinsics[2] = cam->cx;
    cam->intrinsics[4] = cam->fy;
    cam->intrinsics[5] = cam->cy;
    cam->intrinsics[8] = 1;
    for (int i = 0; i < 4; ++i) cam->extrinsics[5 * i] = 1;
    cam->is_identity_extrinsics = 1;
}

int main(void) {
    tvdb_error_t err = {0};
    tvdb_camera_t cam;
    camera(&cam);

    /* Unit quaternion off the axes, anisotropic scale: every entry of the 3x3
     * covariance is non-zero. */
    float rot_q[4] = {0.1743f, -0.0871f, 0.0523f, 0.9792f};
    {
        const float inv = 1.0f / (float)sqrt((double)(rot_q[0] * rot_q[0] + rot_q[1] * rot_q[1] +
                                                      rot_q[2] * rot_q[2] + rot_q[3] * rot_q[3]));
        for (int i = 0; i < 4; ++i) rot_q[i] *= inv;
    }
    float rot_scale[3] = {0.42f, 1.27f, 0.71f};
    float log_scale[3];
    for (int i = 0; i < 3; ++i) log_scale[i] = (float)log2(rot_scale[i]);

    const uint32_t n = 4;
    float means[4 * 3], quats[4 * 4], scales[4 * 3], opacities[4], sh[4 * 3];
    tvdb_gaussian_splat_t splats;
    memset(&splats, 0, sizeof(splats));
    splats.num_gaussians = n;
    splats.means = means;
    splats.quats = quats;
    splats.log_scales = scales;
    splats.logit_opacities = opacities;
    splats.sh_coeffs = sh;

    const float q90[4] = {0, 0, (float)sin(0.25 * 3.14159265358979),
                          (float)cos(0.25 * 3.14159265358979)};
    float q_turned[4];
    quat_mul(q90, rot_q, q_turned);
    const float centres[4][3] = {{0.62f, -0.31f, 2.35f}, /* 0: off-centre */
                                 {0.0f, 0.0f, 2.35f},    /* 1: centred */
                                 {0.0f, 0.0f, 2.35f},    /* 2: centred, turned 90 */
                                 {0.1f, 0.2f, -1.0f}};   /* 3: behind the camera */
    for (uint32_t i = 0; i < n; ++i) {
        memcpy(means + 3 * i, centres[i], sizeof(centres[i]));
        const float *q = i == 2 ? q_turned : rot_q;
        memcpy(quats + 4 * i, q, 4 * sizeof(float));
        memcpy(scales + 3 * i, log_scale, sizeof(log_scale));
        opacities[i] = i == 1 ? 2.0f : 0.0f;
        for (int k = 0; k < 3; ++k) sh[3 * i + k] = 0.25f * (float)(k + 1) - 0.5f * (float)i;
    }

    uint32_t count = 0;
    tvdb_projected_gaussian_t *g = tvdb_gaussian_project(&splats, &cam, &count, &err);
    CHECK(g && count == n);

    /* Off-centre splat: the perspective terms use the xz/yz covariance, so the
     * whole conic has to match the reference. */
    for (uint32_t i = 0; i < 3; ++i) {
        double xy[2], cov2d[3], radius;
        CHECK(reference(means + 3 * i, quats + 4 * i, rot_scale, &cam, xy, cov2d, &radius));
        const double det = cov2d[0] * cov2d[2] - cov2d[1] * cov2d[1];
        CHECK(det > 0);
        CHECK(close_to(g[i].x, xy[0], 2e-3));
        CHECK(close_to(g[i].y, xy[1], 2e-3));
        CHECK(close_to(g[i].depth, means[3 * i + 2], 1e-6));
        /* The projection reports the inverse as (a, b, c) with b on the
         * off-diagonal, so compare relative to the conic's own scale. */
        CHECK(close_to(g[i].conic_a, cov2d[2] / det, 1e-5 * (cov2d[2] / det)));
        CHECK(close_to(g[i].conic_b, -cov2d[1] / det, 1e-5 * (fabs(cov2d[1]) / det) + 1e-9));
        CHECK(close_to(g[i].conic_c, cov2d[0] / det, 1e-5 * (cov2d[0] / det)));
        /* fast_sqrt in the radius keeps this to a few percent. */
        CHECK(close_to(g[i].radius, radius, 0.02 * radius));
    }
    /* A unit-scale splat at f=800, depth 2 must be hundreds of pixels across. */
    {
        float unit_mean[3] = {0, 0, 2.0f}, unit_scale[3] = {1, 1, 1};
        const float unit_q[4] = {0, 0, 0, 1};
        float save_m[3], save_q[4], save_s[3];
        memcpy(save_m, means, sizeof(save_m));
        memcpy(save_q, quats, sizeof(save_q));
        memcpy(save_s, scales, sizeof(save_s));
        memcpy(means, unit_mean, sizeof(unit_mean));
        memcpy(quats, unit_q, sizeof(unit_q));
        for (int k = 0; k < 3; ++k) scales[k] = (float)log2(unit_scale[k]);
        tvdb_projected_gaussian_t *one = tvdb_gaussian_project(&splats, &cam, &count, &err);
        CHECK(one);
        /* 3 sigma of a radius-1 sphere at depth 2 with f=800 is ~1200 px. */
        CHECK(close_to(one[0].radius, 1200.0, 20.0));
        tvdb_projected_gaussian_destroy(one);
        memcpy(means, save_m, sizeof(save_m));
        memcpy(quats, save_q, sizeof(save_q));
        memcpy(scales, save_s, sizeof(save_s));
    }
    /* A 90 degree turn about the view axis swaps the conic's diagonal and
     * negates its off-diagonal (equal focal lengths, centred splat). */
    CHECK(close_to(g[2].conic_a, g[1].conic_c, 1e-5 * g[1].conic_c));
    CHECK(close_to(g[2].conic_c, g[1].conic_a, 1e-5 * g[1].conic_a));
    CHECK(close_to(g[2].conic_b, -g[1].conic_b, 1e-5 * fabs(g[1].conic_b) + 1e-9));
    CHECK(close_to(g[2].radius, g[1].radius, 0.02 * g[1].radius));
    /* Opacity is the sigmoid of the stored logit; features pass through. */
    CHECK(close_to(g[0].opacity, 0.5, 1e-6));
    /* The stored logit is decoded with exp2, matching the shader. */
    CHECK(close_to(g[1].opacity, 1.0 / (1.0 + exp2(-2.0)), 1e-6));
    for (uint32_t i = 0; i < 3; ++i)
        for (int k = 0; k < 3; ++k) CHECK(g[i].feature[k] == sh[3 * i + k]);
    /* Behind the camera: nothing projected, and no leftover fields. */
    for (int k = 0; k < 3; ++k)
        CHECK(g[3].feature[k] == 0 && g[3].x == 0 && g[3].conic_a == 0);
    CHECK(g[3].radius == 0 && g[3].opacity == 0 && g[3].depth == 0);
    tvdb_projected_gaussian_destroy(g);

    /* Depth limits cull on both sides; without SH the feature is white. */
    splats.sh_coeffs = NULL;
    means[0 * 3 + 2] = cam.near;
    means[1 * 3 + 2] = cam.far;
    means[2 * 3 + 2] = 0.5f;
    means[3 * 3 + 2] = 0.5f;
    g = tvdb_gaussian_project(&splats, &cam, &count, &err);
    CHECK(g && count == n);
    CHECK(g[0].radius == 0 && g[1].radius == 0 && g[2].radius > 0);
    CHECK(g[2].feature[0] == 1 && g[2].feature[1] == 0 && g[2].feature[2] == 0);
    tvdb_projected_gaussian_destroy(g);

    /* Argument checks, and an empty projection is valid. */
    memset(err.message, 0, sizeof(err.message));
    CHECK(!tvdb_gaussian_project(NULL, &cam, &count, &err));
    CHECK(err.message[0] != '\0');
    CHECK(!tvdb_gaussian_project(&splats, NULL, &count, &err));
    CHECK(!tvdb_gaussian_project(&splats, &cam, NULL, &err));
    splats.num_gaussians = 0;
    g = tvdb_gaussian_project(&splats, &cam, &count, &err);
    CHECK(g && count == 0);
    tvdb_projected_gaussian_destroy(g);

    puts("gaussian projection contracts passed");
    return 0;
}
