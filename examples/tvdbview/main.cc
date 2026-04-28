#include <glad/glad.h>
#include <GLFW/glfw3.h>

#include "imgui.h"
#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"

#if defined(TVDBVIEW_ENABLE_NFD)
#include <nfd.h>
#endif

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"
#endif
#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic pop
#endif

#include "tinyvdb_io.h"

#if defined(__has_include)
#if __has_include(<vulkan/vulkan.h>)
#define VK_NO_PROTOTYPES
#include <vulkan/vulkan.h>
#define TVDBVIEW_HAS_VULKAN_HEADERS 1
#endif
#endif
#ifndef TVDBVIEW_HAS_VULKAN_HEADERS
#define TVDBVIEW_HAS_VULKAN_HEADERS 0
#endif

#include <algorithm>
#include <array>
#include <cerrno>
#include <cfloat>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <limits>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#if defined(__unix__) || defined(__APPLE__)
#include <dlfcn.h>
#endif

namespace {

#include "generated_vulkan_pathtrace_spv.inc"

const int kWindowWidth = 1280;
const int kWindowHeight = 900;
const std::size_t kMaxDenseVoxels = 256ull * 256ull * 256ull;
const int kHistogramBins = 64;
const float kPi = 3.1415926535f;
const float kCameraFovYRadians = 45.0f * kPi / 180.0f;

struct Vec3 {
  float x;
  float y;
  float z;
};

Vec3 operator+(const Vec3& a, const Vec3& b) {
  return Vec3{a.x + b.x, a.y + b.y, a.z + b.z};
}

Vec3 operator-(const Vec3& a, const Vec3& b) {
  return Vec3{a.x - b.x, a.y - b.y, a.z - b.z};
}

Vec3 operator*(const Vec3& v, float s) {
  return Vec3{v.x * s, v.y * s, v.z * s};
}

float Dot(const Vec3& a, const Vec3& b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

Vec3 Cross(const Vec3& a, const Vec3& b) {
  return Vec3{a.y * b.z - a.z * b.y,
              a.z * b.x - a.x * b.z,
              a.x * b.y - a.y * b.x};
}

float Length(const Vec3& v) {
  return std::sqrt(Dot(v, v));
}

Vec3 Normalize(const Vec3& v) {
  const float len = Length(v);
  if (len < 1.0e-8f) return Vec3{0.0f, 0.0f, 0.0f};
  return v * (1.0f / len);
}

struct Mat4 {
  float m[16];

  static Mat4 Identity() {
    Mat4 r;
    std::memset(r.m, 0, sizeof(r.m));
    r.m[0] = 1.0f;
    r.m[5] = 1.0f;
    r.m[10] = 1.0f;
    r.m[15] = 1.0f;
    return r;
  }

  float& at(int col, int row) { return m[col * 4 + row]; }
  float at(int col, int row) const { return m[col * 4 + row]; }
};

Mat4 operator*(const Mat4& a, const Mat4& b) {
  Mat4 r;
  std::memset(r.m, 0, sizeof(r.m));
  for (int c = 0; c < 4; ++c) {
    for (int row = 0; row < 4; ++row) {
      for (int k = 0; k < 4; ++k) {
        r.m[c * 4 + row] += a.m[k * 4 + row] * b.m[c * 4 + k];
      }
    }
  }
  return r;
}

Mat4 LookAt(const Vec3& eye, const Vec3& target, const Vec3& up) {
  const Vec3 f = Normalize(target - eye);
  const Vec3 s = Normalize(Cross(f, up));
  const Vec3 u = Cross(s, f);

  Mat4 r = Mat4::Identity();
  r.at(0, 0) = s.x;
  r.at(0, 1) = u.x;
  r.at(0, 2) = -f.x;
  r.at(1, 0) = s.y;
  r.at(1, 1) = u.y;
  r.at(1, 2) = -f.y;
  r.at(2, 0) = s.z;
  r.at(2, 1) = u.z;
  r.at(2, 2) = -f.z;
  r.at(3, 0) = -Dot(s, eye);
  r.at(3, 1) = -Dot(u, eye);
  r.at(3, 2) = Dot(f, eye);
  return r;
}

Mat4 Perspective(float fov_y_rad, float aspect, float near_plane, float far_plane) {
  const float f = 1.0f / std::tan(fov_y_rad * 0.5f);
  Mat4 r;
  std::memset(r.m, 0, sizeof(r.m));
  r.at(0, 0) = f / aspect;
  r.at(1, 1) = f;
  r.at(2, 2) = (far_plane + near_plane) / (near_plane - far_plane);
  r.at(2, 3) = -1.0f;
  r.at(3, 2) = (2.0f * far_plane * near_plane) / (near_plane - far_plane);
  return r;
}

struct Bounds {
  Vec3 min;
  Vec3 max;
  bool valid;

  Bounds()
      : min{1.0e30f, 1.0e30f, 1.0e30f},
        max{-1.0e30f, -1.0e30f, -1.0e30f},
        valid(false) {}

  void expand(const Vec3& p) {
    min.x = std::min(min.x, p.x);
    min.y = std::min(min.y, p.y);
    min.z = std::min(min.z, p.z);
    max.x = std::max(max.x, p.x);
    max.y = std::max(max.y, p.y);
    max.z = std::max(max.z, p.z);
    valid = true;
  }

  void expand(const Bounds& b) {
    if (!b.valid) return;
    expand(b.min);
    expand(b.max);
  }

  Vec3 center() const {
    return (min + max) * 0.5f;
  }

  Vec3 extent() const {
    return max - min;
  }

  float radius() const {
    return valid ? std::max(Length(extent()) * 0.5f, 0.001f) : 1.0f;
  }
};

struct OrbitCamera {
  float longitude = 45.0f;
  float latitude = 25.0f;
  float distance = 8.0f;
  Vec3 target{0.0f, 0.0f, 0.0f};

  Vec3 eye() const {
    const float lon = longitude * 3.1415926535f / 180.0f;
    const float lat = latitude * 3.1415926535f / 180.0f;
    const float cos_lat = std::cos(lat);
    return Vec3{
        target.x + distance * cos_lat * std::sin(lon),
        target.y + distance * std::sin(lat),
        target.z + distance * cos_lat * std::cos(lon),
    };
  }

  Mat4 viewProjection(float aspect) const {
    const Mat4 view = LookAt(eye(), target, Vec3{0.0f, 1.0f, 0.0f});
    const float far_plane = std::max(2000.0f, distance * 8.0f + 100.0f);
    const Mat4 proj = Perspective(kCameraFovYRadians, aspect, 0.01f, far_plane);
    return proj * view;
  }

  void resetToBounds(const Bounds& bounds) {
    target = bounds.valid ? bounds.center() : Vec3{0.0f, 0.0f, 0.0f};
    distance = std::max(bounds.radius() * 2.4f, 1.0f);
    longitude = 45.0f;
    latitude = 25.0f;
  }

  void localAxes(Vec3* right, Vec3* up) const {
    const Vec3 forward = Normalize(target - eye());
    *right = Normalize(Cross(forward, Vec3{0.0f, 1.0f, 0.0f}));
    if (Length(*right) < 1.0e-6f) *right = Vec3{1.0f, 0.0f, 0.0f};
    *up = Cross(*right, forward);
  }
};

struct VolumeNodeBox {
  Vec3 min;
  Vec3 max;
  int level;
};

struct VolumeData {
  std::string name;
  int dim[3] = {0, 0, 0};
  int origin_index[3] = {0, 0, 0};
  float voxel_size[3] = {1.0f, 1.0f, 1.0f};
  float translation[3] = {0.0f, 0.0f, 0.0f};
  std::vector<float> density;
  float min_value = 0.0f;
  float max_value = 1.0f;
  float mean_value = 0.0f;
  float non_background_fraction = 0.0f;
  float histogram_min = 0.0f;
  float histogram_max = 1.0f;
  std::vector<float> histogram;
  bool has_active_bbox = false;
  int active_index_min[3] = {0, 0, 0};
  int active_index_max[3] = {0, 0, 0};
  float active_uvw_min[3] = {0.0f, 0.0f, 0.0f};
  float active_uvw_max[3] = {1.0f, 1.0f, 1.0f};
  float background = 0.0f;
  int downsample_stride = 1;
  bool is_level_set = false;
  Bounds world_bounds;
  std::vector<VolumeNodeBox> node_boxes;
  int max_level = 0;

  std::string emission_name;
  std::vector<float> emission;
  float emission_min = 0.0f;
  float emission_max = 1.0f;
  float emission_background = 0.0f;

  std::string vector_name;
  std::vector<float> vector3;
  float vector_max_len = 0.0f;
};

struct SceneData {
  std::vector<VolumeData> volumes;
  Bounds bounds;
  std::vector<std::string> notes;
};

struct LineMesh {
  GLuint vao = 0;
  GLuint vbo = 0;
  GLuint ebo = 0;
  GLsizei index_count = 0;
};

struct GpuVolume {
  GLuint texture = 0;
  GLuint emission_texture = 0;
  GLuint vector_texture = 0;
  GLuint vao = 0;
  GLuint vbo = 0;
  GLuint ebo = 0;
  GLsizei index_count = 0;
  LineMesh internal_lines;
  LineMesh leaf_lines;
  LineMesh dense_bounds_lines;
  Bounds world_bounds;
  float value_offset = 0.0f;
  float value_scale = 1.0f;
  float sdf_band_scale = 1.0f;
  float emission_offset = 0.0f;
  float emission_scale = 1.0f;
  float vector_len_scale = 1.0f;
  bool has_density = false;
  bool has_emission = false;
  bool has_vector = false;
  bool is_level_set = false;
};

enum class VolumeRenderMode {
  Volume,
  VolumeWithGrid,
  GridOnly,
};

enum class VolumeColorMode {
  Density = 0,
  Jet = 1,
  Blackbody = 2,
  Vector = 3,
};

enum class VolumeRayMode {
  Composite = 0,
  Mip = 1,
  Iso = 2,
  PathTraceCpu = 3,
};

struct VulkanPathTraceBackend;

struct AppState {
  GLFWwindow* window = nullptr;
  int window_width = kWindowWidth;
  int window_height = kWindowHeight;
  int framebuffer_width = kWindowWidth;
  int framebuffer_height = kWindowHeight;
  GLuint volume_program = 0;
  GLuint line_program = 0;
  GLuint image_program = 0;
  GLuint path_trace_compute_program = 0;
  GLuint image_vao = 0;
  GLuint path_trace_texture = 0;
  GLuint path_trace_accum_texture = 0;
  bool path_trace_compute_available = false;
  VulkanPathTraceBackend* vulkan_path_trace = nullptr;
  bool path_trace_vulkan_available = false;
  std::vector<GpuVolume> gpu_volumes;
  SceneData scene;
  OrbitCamera camera;
  bool left_mouse_down = false;
  bool middle_mouse_down = false;
  bool right_mouse_down = false;
  double last_cursor_x = 0.0;
  double last_cursor_y = 0.0;
  VolumeRenderMode render_mode = VolumeRenderMode::VolumeWithGrid;
  VolumeColorMode color_mode = VolumeColorMode::Density;
  std::size_t active_volume = 0;
  float density_gain = 2.0f;
  bool manual_window = false;
  float window_min = 0.0f;
  float window_max = 1.0f;
  float value_gamma = 1.0f;
  float opacity_power = 1.0f;
  bool invert_values = false;
  int sample_steps = 128;
  VolumeRayMode ray_mode = VolumeRayMode::Composite;
  float iso_threshold = 0.5f;
  int path_trace_scale = 2;
  int path_trace_rows_per_frame = 24;
  int path_trace_max_depth = 2;
  int path_trace_backend = 0;  // 0=auto, 1=OpenGL compute, 2=CPU, 3=Vulkan compute.
  float path_trace_sun_angle = 35.0f;
  float path_trace_sun_azimuth = 45.0f;
  float path_trace_sun_strength = 4.0f;
  float path_trace_sky_strength = 0.7f;
  float path_trace_albedo = 0.9f;
  int path_trace_width = 0;
  int path_trace_height = 0;
  int path_trace_next_row = 0;
  int path_trace_completed_passes = 0;
  int path_trace_capture_samples = 0;
  std::string path_trace_last_backend = "none";
  std::string path_trace_fingerprint;
  std::vector<Vec3> path_trace_accum;
  std::vector<uint32_t> path_trace_sample_counts;
  std::vector<uint8_t> path_trace_rgba;
  bool shade_enabled = true;
  float shade_strength = 0.65f;
  Vec3 light_dir{0.4f, 0.6f, 0.7f};
  bool sdf_fog_mode = false;
  bool show_internal_boxes = true;
  bool show_leaf_boxes = true;
  bool show_dense_bounds = true;
  bool show_hud = true;
  bool show_control_panel = true;
  int slice_axis = 0;  // 0=off, 1=x, 2=y, 3=z
  float slice_pos = 0.5f;
  float slice_thickness = 1.0f;
  bool clip_enabled = false;
  float clip_min[3] = {0.0f, 0.0f, 0.0f};
  float clip_max[3] = {1.0f, 1.0f, 1.0f};
  OrbitCamera camera_bookmarks[3];
  bool has_camera_bookmark[3] = {false, false, false};
  int screenshot_counter = 0;
  bool pending_capture = false;
  bool quit_after_capture = false;
  std::string capture_path;
  bool has_probe = false;
  Vec3 probe_world{0.0f, 0.0f, 0.0f};
  Vec3 probe_uvw{0.0f, 0.0f, 0.0f};
  int probe_index[3] = {0, 0, 0};
  float probe_value = 0.0f;
  int probe_mode = 1;  // 0=midpoint, 1=max visible value along ray.
  std::string current_path;
#if defined(TVDBVIEW_ENABLE_NFD)
  bool nfd_initialized = false;
#endif
};

struct CliOptions {
  std::string input_path;
  std::string grid_selector;
  bool has_grid = false;
  bool has_color = false;
  VolumeColorMode color_mode = VolumeColorMode::Density;
  bool has_render_mode = false;
  VolumeRenderMode render_mode = VolumeRenderMode::VolumeWithGrid;
  bool has_gain = false;
  float density_gain = 2.0f;
  bool has_window = false;
  float window_min = 0.0f;
  float window_max = 1.0f;
  bool has_percentile_window = false;
  float window_percentile_min = 1.0f;
  float window_percentile_max = 99.0f;
  bool has_gamma = false;
  float value_gamma = 1.0f;
  bool has_opacity_power = false;
  float opacity_power = 1.0f;
  bool invert_values = false;
  bool has_steps = false;
  int sample_steps = 128;
  bool has_ray_mode = false;
  VolumeRayMode ray_mode = VolumeRayMode::Composite;
  bool has_iso_threshold = false;
  float iso_threshold = 0.5f;
  bool has_path_trace_scale = false;
  int path_trace_scale = 2;
  bool has_path_trace_rows = false;
  int path_trace_rows_per_frame = 24;
  bool has_path_trace_depth = false;
  int path_trace_max_depth = 2;
  bool has_path_trace_backend = false;
  int path_trace_backend = 0;
  bool has_path_trace_capture_samples = false;
  int path_trace_capture_samples = 0;
  bool has_sun = false;
  float path_trace_sun_angle = 35.0f;
  float path_trace_sun_azimuth = 45.0f;
  bool has_sun_strength = false;
  float path_trace_sun_strength = 4.0f;
  bool has_sky_strength = false;
  float path_trace_sky_strength = 0.7f;
  bool has_path_trace_albedo = false;
  float path_trace_albedo = 0.9f;
  bool has_shade_enabled = false;
  bool shade_enabled = true;
  bool has_shade_strength = false;
  float shade_strength = 0.65f;
  bool has_light_dir = false;
  Vec3 light_dir{0.4f, 0.6f, 0.7f};
  bool has_slice = false;
  int slice_axis = 0;
  float slice_pos = 0.5f;
  float slice_thickness = 0.04f;
  bool has_clip = false;
  float clip_min[3] = {0.0f, 0.0f, 0.0f};
  float clip_max[3] = {1.0f, 1.0f, 1.0f};
  bool clip_active = false;
  bool has_capture = false;
  std::string capture_path;
  bool quit_after_capture = false;
  bool no_grid = false;
  bool sdf_fog_mode = false;
  bool hide_internal_boxes = false;
  bool hide_leaf_boxes = false;
  bool hide_dense_bounds = false;
  bool hide_hud = false;
  bool hide_panel = false;
  bool has_camera = false;
  float camera_longitude = 45.0f;
  float camera_latitude = 25.0f;
  float camera_distance = 8.0f;
  Vec3 camera_target{0.0f, 0.0f, 0.0f};
  bool has_window_size = false;
  int window_width = kWindowWidth;
  int window_height = kWindowHeight;
  bool show_help = false;
};

const char* kVolumeVs = R"(
#version 330 core
layout(location = 0) in vec3 aPos;

uniform mat4 uModel;
uniform mat4 uVP;

out vec3 vWorldPos;

void main() {
  vec4 wp = uModel * vec4(aPos, 1.0);
  vWorldPos = wp.xyz;
  gl_Position = uVP * wp;
}
)";

const char* kVolumeFs = R"(
#version 330 core
in vec3 vWorldPos;

uniform sampler3D uVolume;
uniform sampler3D uEmission;
uniform int uHasEmission;
uniform float uEmissionOffset;
uniform float uEmissionScale;
uniform sampler3D uVectorTex;
uniform int uHasVector;
uniform float uVectorLenScale;
uniform vec3 uCameraPos;
uniform vec3 uVolumeMin;
uniform vec3 uVolumeMax;
uniform float uValueOffset;
uniform float uValueScale;
uniform float uDensityGain;
uniform float uValueGamma;
uniform float uOpacityPower;
uniform int uInvertValues;
uniform int uStepCount;
uniform int uRayMode;
uniform float uIsoThreshold;
uniform int uShadeEnabled;
uniform float uShadeStrength;
uniform vec3 uLightDir;
uniform vec3 uTexelSize;
uniform int uFogFromSdf;
uniform float uSdfBandScale;
uniform int uColorMode;
uniform vec3 uClipMin;
uniform vec3 uClipMax;
uniform int uSliceAxis;
uniform float uSlicePos;
uniform float uSliceThickness;

out vec4 FragColor;

vec3 jetColor(float t) {
  t = clamp(t, 0.0, 1.0);
  float r = clamp(1.5 - abs(4.0 * t - 3.0), 0.0, 1.0);
  float g = clamp(1.5 - abs(4.0 * t - 2.0), 0.0, 1.0);
  float b = clamp(1.5 - abs(4.0 * t - 1.0), 0.0, 1.0);
  return vec3(r, g, b);
}

vec3 blackbody(float t) {
  t = clamp(t, 0.0, 1.0);
  vec3 dark = vec3(0.0, 0.0, 0.0);
  vec3 red = vec3(1.0, 0.12, 0.02);
  vec3 orange = vec3(1.0, 0.55, 0.05);
  vec3 yellow = vec3(1.0, 0.92, 0.35);
  vec3 white = vec3(1.0, 1.0, 0.95);
  if (t < 0.25) return mix(dark, red, t / 0.25);
  if (t < 0.5) return mix(red, orange, (t - 0.25) / 0.25);
  if (t < 0.75) return mix(orange, yellow, (t - 0.5) / 0.25);
  return mix(yellow, white, (t - 0.75) / 0.25);
}

float normalizedValue(vec3 uvw) {
  float raw = texture(uVolume, clamp(uvw, vec3(0.0), vec3(1.0))).r;
  float norm = (uFogFromSdf == 1)
      ? clamp(-raw * uSdfBandScale, 0.0, 1.0)
      : clamp((raw - uValueOffset) * uValueScale, 0.0, 1.0);
  if (uInvertValues == 1) {
    norm = 1.0 - norm;
  }
  return pow(norm, max(uValueGamma, 1e-4));
}

vec3 shadeSample(vec3 color, vec3 uvw, vec3 viewDir) {
  if (uShadeEnabled == 0 || uShadeStrength <= 0.0) return color;
  float dx = normalizedValue(uvw + vec3(uTexelSize.x, 0.0, 0.0)) -
             normalizedValue(uvw - vec3(uTexelSize.x, 0.0, 0.0));
  float dy = normalizedValue(uvw + vec3(0.0, uTexelSize.y, 0.0)) -
             normalizedValue(uvw - vec3(0.0, uTexelSize.y, 0.0));
  float dz = normalizedValue(uvw + vec3(0.0, 0.0, uTexelSize.z)) -
             normalizedValue(uvw - vec3(0.0, 0.0, uTexelSize.z));
  vec3 g = vec3(dx, dy, dz);
  float glen = length(g);
  if (glen < 1e-6) return color;
  vec3 n = -g / glen;
  vec3 l = length(uLightDir) > 1e-6 ? normalize(uLightDir) : vec3(0.4, 0.6, 0.7);
  vec3 v = normalize(-viewDir);
  float diffuse = max(dot(n, l), 0.0);
  float rim = pow(1.0 - max(dot(n, v), 0.0), 2.0);
  float shade = 0.24 + 0.78 * diffuse + 0.18 * rim;
  return color * mix(1.0, shade, clamp(uShadeStrength, 0.0, 1.0));
}

void main() {
  vec3 ro = uCameraPos;
  vec3 rd = normalize(vWorldPos - uCameraPos);
  vec3 invRd = 1.0 / rd;
  vec3 t0 = (uVolumeMin - ro) * invRd;
  vec3 t1 = (uVolumeMax - ro) * invRd;
  vec3 tmn = min(t0, t1);
  vec3 tmx = max(t0, t1);
  float tEnter = max(max(tmn.x, tmn.y), tmn.z);
  float tExit = min(min(tmx.x, tmx.y), tmx.z);
  tEnter = max(tEnter, 0.0);
  if (tEnter >= tExit) discard;

  const int kMaxSteps = 512;
  int steps = clamp(uStepCount, 1, kMaxSteps);
  float dt = (tExit - tEnter) / float(steps);
  float transmittance = 1.0;
  vec3 accumColor = vec3(0.0);
  float mipValue = -1.0;
  vec3 mipColor = vec3(0.0);
  float isoHit = 0.0;
  vec3 isoColor = vec3(0.0);
  vec3 extent = uVolumeMax - uVolumeMin;
  for (int i = 0; i < kMaxSteps; ++i) {
    if (i >= steps) break;
    float t = tEnter + (float(i) + 0.5) * dt;
    vec3 p = ro + rd * t;
    vec3 uvw = (p - uVolumeMin) / extent;
    if (any(lessThan(uvw, uClipMin)) || any(greaterThan(uvw, uClipMax))) {
      continue;
    }
    if (uSliceAxis > 0) {
      float s = (uSliceAxis == 1) ? uvw.x : ((uSliceAxis == 2) ? uvw.y : uvw.z);
      if (abs(s - uSlicePos) > uSliceThickness * 0.5) {
        continue;
      }
    }
    float raw = texture(uVolume, uvw).r;
    float norm = normalizedValue(uvw);
    float density = pow(norm, max(uOpacityPower, 1e-4)) * uDensityGain;
    float colorParam = norm;
    if (uHasEmission == 1) {
      float rawE = texture(uEmission, uvw).r;
      colorParam = clamp((rawE - uEmissionOffset) * uEmissionScale, 0.0, 1.0);
    }

    vec3 sampleColor;
    if (uColorMode == 3 && uHasVector == 1) {
      vec3 v = texture(uVectorTex, uvw).rgb;
      float lenv = length(v);
      vec3 dir = v / max(lenv, 1e-6);
      sampleColor = 0.5 + 0.5 * dir;
      density = clamp(lenv * uVectorLenScale, 0.0, 1.0) * uDensityGain;
    } else if (uColorMode == 1) {
      sampleColor = jetColor(colorParam);
    } else if (uColorMode == 2) {
      sampleColor = blackbody(colorParam);
    } else {
      sampleColor = vec3(norm);
    }
    sampleColor = shadeSample(sampleColor, uvw, rd);

    if (uRayMode == 1) {
      if (colorParam > mipValue) {
        mipValue = colorParam;
        mipColor = sampleColor;
      }
      continue;
    }
    if (uRayMode == 2) {
      if (isoHit < 0.5 && norm >= uIsoThreshold) {
        isoHit = 1.0;
        isoColor = sampleColor;
        break;
      }
      continue;
    }

    float alpha = 1.0 - exp(-density * dt);
    accumColor += transmittance * alpha * sampleColor;
    transmittance *= (1.0 - alpha);
    if (transmittance < 0.005) break;
  }
  if (uRayMode == 1) {
    if (mipValue < 0.0) discard;
    FragColor = vec4(mipColor, clamp(mipValue, 0.0, 1.0));
    return;
  }
  if (uRayMode == 2) {
    if (isoHit < 0.5) discard;
    FragColor = vec4(isoColor, 1.0);
    return;
  }
  float opacity = 1.0 - transmittance;
  if (opacity < 1e-3) discard;
  FragColor = vec4(accumColor, opacity);
}
)";

const char* kLineVs = R"(
#version 330 core
layout(location = 0) in vec3 aPos;
layout(location = 1) in vec3 aColor;

uniform mat4 uVP;

out vec3 vColor;

void main() {
  vColor = aColor;
  gl_Position = uVP * vec4(aPos, 1.0);
}
)";

const char* kLineFs = R"(
#version 330 core
in vec3 vColor;
out vec4 FragColor;

void main() {
  FragColor = vec4(vColor, 1.0);
}
)";

const char* kImageVs = R"(
#version 330 core
const vec2 kPos[3] = vec2[3](
  vec2(-1.0, -1.0),
  vec2( 3.0, -1.0),
  vec2(-1.0,  3.0)
);
out vec2 vUv;
void main() {
  vec2 p = kPos[gl_VertexID];
  vUv = p * 0.5 + 0.5;
  gl_Position = vec4(p, 0.0, 1.0);
}
)";

const char* kImageFs = R"(
#version 330 core
uniform sampler2D uImage;
in vec2 vUv;
out vec4 FragColor;
void main() {
  FragColor = texture(uImage, vUv);
}
)";

const char* kPathTraceCs = R"(
#version 430 core
layout(local_size_x = 8, local_size_y = 8) in;
layout(rgba32f, binding = 0) uniform image2D uAccum;
layout(rgba8, binding = 1) uniform image2D uOutput;
uniform sampler3D uVolume;
uniform ivec2 uImageSize;
uniform uint uSampleIndex;
uniform vec3 uCameraPos;
uniform vec3 uCameraForward;
uniform vec3 uCameraRight;
uniform vec3 uCameraUp;
uniform float uTanHalfFovY;
uniform vec3 uVolumeMin;
uniform vec3 uVolumeMax;
uniform float uValueOffset;
uniform float uValueScale;
uniform float uDensityGain;
uniform float uValueGamma;
uniform float uOpacityPower;
uniform int uInvertValues;
uniform int uStepCount;
uniform vec3 uClipMin;
uniform vec3 uClipMax;
uniform int uSliceAxis;
uniform float uSlicePos;
uniform float uSliceThickness;
uniform float uSunElevation;
uniform float uSunAzimuth;
uniform float uSunStrength;
uniform float uSkyStrength;
uniform float uAlbedo;

uint hash_u32(uint x) {
  x ^= x >> 16;
  x *= 0x7feb352du;
  x ^= x >> 15;
  x *= 0x846ca68bu;
  x ^= x >> 16;
  return x;
}

float rand(inout uint s) {
  s = hash_u32(s + 0x9e3779b9u);
  return float(s & 0x00ffffffu) / float(0x01000000u);
}

vec3 sunDir() {
  float elev = radians(uSunElevation);
  float az = radians(uSunAzimuth);
  float ce = cos(elev);
  return normalize(vec3(ce * sin(az), sin(elev), ce * cos(az)));
}

vec3 environment(vec3 d) {
  vec3 sd = sunDir();
  float up = clamp(d.y * 0.5 + 0.5, 0.0, 1.0);
  vec3 sky = mix(vec3(0.78, 0.86, 1.0), vec3(0.10, 0.32, 0.85), up) * uSkyStrength;
  float disk = pow(max(dot(normalize(d), sd), 0.0), 900.0);
  return sky + vec3(1.0, 0.86, 0.62) * (disk * uSunStrength);
}

bool intersectBox(vec3 ro, vec3 rd, out float tEnter, out float tExit) {
  vec3 invRd = 1.0 / rd;
  vec3 t0 = (uVolumeMin - ro) * invRd;
  vec3 t1 = (uVolumeMax - ro) * invRd;
  vec3 tmn = min(t0, t1);
  vec3 tmx = max(t0, t1);
  tEnter = max(max(tmn.x, tmn.y), tmn.z);
  tExit = min(min(tmx.x, tmx.y), tmx.z);
  tEnter = max(tEnter, 0.0);
  return tEnter < tExit;
}

float normalizedValue(vec3 uvw) {
  if (any(lessThan(uvw, uClipMin)) || any(greaterThan(uvw, uClipMax))) return 0.0;
  if (uSliceAxis > 0) {
    float s = (uSliceAxis == 1) ? uvw.x : ((uSliceAxis == 2) ? uvw.y : uvw.z);
    if (abs(s - uSlicePos) > uSliceThickness * 0.5) return 0.0;
  }
  float norm = clamp((texture(uVolume, clamp(uvw, vec3(0.0), vec3(1.0))).r - uValueOffset) *
                     uValueScale, 0.0, 1.0);
  if (uInvertValues == 1) norm = 1.0 - norm;
  return pow(norm, max(uValueGamma, 1e-4));
}

vec3 valueColor(float t) {
  t = clamp(t, 0.0, 1.0);
  return vec3(t);
}

void main() {
  ivec2 pix = ivec2(gl_GlobalInvocationID.xy);
  if (pix.x >= uImageSize.x || pix.y >= uImageSize.y) return;
  uint rng = hash_u32(uint(pix.x + 1) * 1973u ^ uint(pix.y + 1) * 9277u ^
                      (uSampleIndex + 1u) * 26699u);
  vec2 jitter = vec2(rand(rng), rand(rng));
  vec2 p = (vec2(pix) + jitter) / vec2(uImageSize);
  vec2 ndc = vec2(p.x * 2.0 - 1.0, 1.0 - p.y * 2.0);
  float aspect = float(uImageSize.x) / max(float(uImageSize.y), 1.0);
  vec3 rd = normalize(uCameraForward + uCameraRight * (ndc.x * aspect * uTanHalfFovY) +
                      uCameraUp * (ndc.y * uTanHalfFovY));
  float tEnter = 0.0;
  float tExit = 0.0;
  vec3 color = vec3(0.0);
  if (intersectBox(uCameraPos, rd, tEnter, tExit)) {
    int steps = clamp(uStepCount, 8, 512);
    float dt = (tExit - tEnter) / float(steps);
    vec3 extent = uVolumeMax - uVolumeMin;
    float maxExtent = max(extent.x, max(extent.y, extent.z));
    float tr = 1.0;
    vec3 sun = sunDir();
    for (int i = 0; i < 512; ++i) {
      if (i >= steps) break;
      float t = tEnter + (float(i) + rand(rng)) * dt;
      vec3 pos = uCameraPos + rd * t;
      vec3 uvw = (pos - uVolumeMin) / extent;
      float n = normalizedValue(uvw);
      float sigma = pow(n, max(uOpacityPower, 1e-4)) * uDensityGain / max(maxExtent, 1e-4);
      float alpha = 1.0 - exp(-sigma * dt);
      vec3 direct = vec3(1.0, 0.86, 0.62) * (uSunStrength * max(dot(rd, sun) * 0.25 + 0.75, 0.0)) +
                    environment(vec3(0.0, 1.0, 0.0)) * 0.18;
      color += tr * alpha * uAlbedo * valueColor(n) * direct;
      tr *= (1.0 - alpha);
      if (tr < 0.003) break;
    }
    color += tr * environment(rd);
  } else {
    color = environment(rd);
  }
  vec4 prev = imageLoad(uAccum, pix);
  float sampleCount = float(uSampleIndex);
  vec3 avg = (prev.rgb * sampleCount + max(color, vec3(0.0))) / (sampleCount + 1.0);
  imageStore(uAccum, pix, vec4(avg, 1.0));
  vec3 mapped = pow(max(avg, vec3(0.0)), vec3(1.0 / 2.2));
  imageStore(uOutput, pix, vec4(clamp(mapped, 0.0, 1.0), 1.0));
}
)";

const char* ColorModeLabel(VolumeColorMode mode) {
  switch (mode) {
    case VolumeColorMode::Density: return "density";
    case VolumeColorMode::Jet: return "jet";
    case VolumeColorMode::Blackbody: return "blackbody";
    case VolumeColorMode::Vector: return "vector";
  }
  return "density";
}

const char* RenderModeLabel(VolumeRenderMode mode) {
  switch (mode) {
    case VolumeRenderMode::Volume: return "volume";
    case VolumeRenderMode::VolumeWithGrid: return "volume+grid";
    case VolumeRenderMode::GridOnly: return "grid";
  }
  return "volume";
}

const char* RayModeLabel(VolumeRayMode mode) {
  switch (mode) {
    case VolumeRayMode::Composite: return "composite";
    case VolumeRayMode::Mip: return "mip";
    case VolumeRayMode::Iso: return "iso";
    case VolumeRayMode::PathTraceCpu: return "pathtrace-cpu";
  }
  return "composite";
}

VolumeColorMode NextColorMode(VolumeColorMode mode) {
  switch (mode) {
    case VolumeColorMode::Density: return VolumeColorMode::Jet;
    case VolumeColorMode::Jet: return VolumeColorMode::Blackbody;
    case VolumeColorMode::Blackbody: return VolumeColorMode::Vector;
    case VolumeColorMode::Vector: return VolumeColorMode::Density;
  }
  return VolumeColorMode::Density;
}

VolumeRayMode NextRayMode(VolumeRayMode mode) {
  switch (mode) {
    case VolumeRayMode::Composite: return VolumeRayMode::Mip;
    case VolumeRayMode::Mip: return VolumeRayMode::Iso;
    case VolumeRayMode::Iso: return VolumeRayMode::PathTraceCpu;
    case VolumeRayMode::PathTraceCpu: return VolumeRayMode::Composite;
  }
  return VolumeRayMode::Composite;
}

VolumeRenderMode NextRenderMode(VolumeRenderMode mode) {
  switch (mode) {
    case VolumeRenderMode::Volume: return VolumeRenderMode::VolumeWithGrid;
    case VolumeRenderMode::VolumeWithGrid: return VolumeRenderMode::GridOnly;
    case VolumeRenderMode::GridOnly: return VolumeRenderMode::Volume;
  }
  return VolumeRenderMode::Volume;
}

void PrintControls() {
  std::cout
      << "Controls:\n"
      << "  left drag        orbit\n"
      << "  middle/right drag pan\n"
      << "  wheel            zoom\n"
      << "  Ctrl+left click  probe selected grid value\n"
      << "  O                open VDB\n"
      << "  0-9              select VDB attribute/grid\n"
      << "  X/Y/Z, \\         slice axis x/y/z/off\n"
      << "  , / .            move slice\n"
      << "  - / =            slice thickness down/up\n"
      << "  K                toggle clip box\n"
      << "  U / J            tighten/loosen clip box\n"
      << "  I / L / B        toggle internal/leaf/dense bboxes\n"
      << "  V                cycle volume/grid display\n"
      << "  C                cycle color mode\n"
      << "  M                cycle ray/pathtrace mode\n"
      << "  [ / ]            density gain down/up\n"
      << "  P                save PNG screenshot\n"
      << "  F                frame selected grid\n"
      << "  F1/F2/F3         front/top/side camera\n"
      << "  Ctrl+F1..F3      save camera bookmark\n"
      << "  Shift+F1..F3     load camera bookmark\n"
      << "  S                toggle SDF fog mode\n"
      << "  R                reset camera\n"
      << "  H                print controls\n"
      << "  Esc              quit\n";
}

const char* SliceAxisLabel(int axis) {
  switch (axis) {
    case 1: return "x";
    case 2: return "y";
    case 3: return "z";
    default: return "off";
  }
}

bool ParseFloatArg(const std::string& text, float* value) {
  if (!value || text.empty()) return false;
  char* end = nullptr;
  errno = 0;
  const float parsed = std::strtof(text.c_str(), &end);
  if (errno != 0 || end == text.c_str() || *end != '\0') return false;
  *value = parsed;
  return true;
}

bool ParseIntArg(const std::string& text, int* value) {
  if (!value || text.empty()) return false;
  char* end = nullptr;
  errno = 0;
  const long parsed = std::strtol(text.c_str(), &end, 10);
  if (errno != 0 || end == text.c_str() || *end != '\0') return false;
  *value = static_cast<int>(parsed);
  return true;
}

bool ParseColorModeArg(const std::string& text, VolumeColorMode* mode) {
  if (text == "density") {
    *mode = VolumeColorMode::Density;
  } else if (text == "jet") {
    *mode = VolumeColorMode::Jet;
  } else if (text == "blackbody") {
    *mode = VolumeColorMode::Blackbody;
  } else if (text == "vector") {
    *mode = VolumeColorMode::Vector;
  } else {
    return false;
  }
  return true;
}

bool ParseRenderModeArg(const std::string& text, VolumeRenderMode* mode) {
  if (text == "volume") {
    *mode = VolumeRenderMode::Volume;
  } else if (text == "volume+grid") {
    *mode = VolumeRenderMode::VolumeWithGrid;
  } else if (text == "grid") {
    *mode = VolumeRenderMode::GridOnly;
  } else {
    return false;
  }
  return true;
}

bool ParseRayModeArg(const std::string& text, VolumeRayMode* mode) {
  if (text == "composite") {
    *mode = VolumeRayMode::Composite;
  } else if (text == "mip") {
    *mode = VolumeRayMode::Mip;
  } else if (text == "iso") {
    *mode = VolumeRayMode::Iso;
  } else if (text == "pathtrace" || text == "pathtrace-cpu" || text == "pt") {
    *mode = VolumeRayMode::PathTraceCpu;
  } else {
    return false;
  }
  return true;
}

bool ParseSliceArg(const std::string& text, int* axis, float* pos, float* thickness) {
  const std::size_t p0 = text.find(':');
  if (p0 == std::string::npos || p0 == 0) return false;
  const std::size_t p1 = text.find(':', p0 + 1);
  const std::string axis_text = text.substr(0, p0);
  if (axis_text == "x") {
    *axis = 1;
  } else if (axis_text == "y") {
    *axis = 2;
  } else if (axis_text == "z") {
    *axis = 3;
  } else if (axis_text == "off") {
    *axis = 0;
  } else {
    return false;
  }
  const std::string pos_text =
      text.substr(p0 + 1, p1 == std::string::npos ? std::string::npos : p1 - p0 - 1);
  if (!ParseFloatArg(pos_text, pos)) return false;
  if (p1 != std::string::npos) {
    if (!ParseFloatArg(text.substr(p1 + 1), thickness)) return false;
  }
  *pos = std::max(0.0f, std::min(1.0f, *pos));
  *thickness = std::max(0.0025f, std::min(1.0f, *thickness));
  return true;
}

bool ParseVec3Csv(const std::string& text, float v[3]) {
  std::size_t start = 0;
  for (int i = 0; i < 3; ++i) {
    const std::size_t comma = text.find(',', start);
    if (i < 2 && comma == std::string::npos) return false;
    if (i == 2 && comma != std::string::npos) return false;
    const std::string part =
        text.substr(start, comma == std::string::npos ? std::string::npos : comma - start);
    if (!ParseFloatArg(part, &v[i])) return false;
    start = comma + 1;
  }
  return true;
}

bool ParseClipArg(const std::string& text, float mn[3], float mx[3]) {
  const std::size_t colon = text.find(':');
  if (colon == std::string::npos) return false;
  if (!ParseVec3Csv(text.substr(0, colon), mn)) return false;
  if (!ParseVec3Csv(text.substr(colon + 1), mx)) return false;
  for (int i = 0; i < 3; ++i) {
    mn[i] = std::max(0.0f, std::min(1.0f, mn[i]));
    mx[i] = std::max(0.0f, std::min(1.0f, mx[i]));
    if (mn[i] > mx[i]) std::swap(mn[i], mx[i]);
  }
  return true;
}

bool ParseRangeArg(const std::string& text, float* mn, float* mx) {
  const std::size_t colon = text.find(':');
  if (colon == std::string::npos) return false;
  if (!ParseFloatArg(text.substr(0, colon), mn)) return false;
  if (!ParseFloatArg(text.substr(colon + 1), mx)) return false;
  if (*mn > *mx) std::swap(*mn, *mx);
  return true;
}

bool ParsePairArg(const std::string& text, float* a, float* b) {
  const std::size_t colon = text.find(':');
  if (colon == std::string::npos) return false;
  if (!ParseFloatArg(text.substr(0, colon), a)) return false;
  if (!ParseFloatArg(text.substr(colon + 1), b)) return false;
  return true;
}

bool ParseCameraArg(const std::string& text, float* longitude, float* latitude,
                    float* distance, Vec3* target) {
  const std::size_t colon = text.find(':');
  if (colon == std::string::npos) return false;
  float orbit[3] = {};
  float tgt[3] = {};
  if (!ParseVec3Csv(text.substr(0, colon), orbit)) return false;
  if (!ParseVec3Csv(text.substr(colon + 1), tgt)) return false;
  *longitude = orbit[0];
  *latitude = std::max(-89.0f, std::min(89.0f, orbit[1]));
  *distance = std::max(0.001f, orbit[2]);
  *target = Vec3{tgt[0], tgt[1], tgt[2]};
  return true;
}

bool ParseWindowSizeArg(const std::string& text, int* width, int* height) {
  const std::size_t x = text.find('x');
  if (x == std::string::npos) return false;
  if (!ParseIntArg(text.substr(0, x), width)) return false;
  if (!ParseIntArg(text.substr(x + 1), height)) return false;
  *width = std::max(64, std::min(16384, *width));
  *height = std::max(64, std::min(16384, *height));
  return true;
}

bool IsOption(const char* arg) {
  return arg && arg[0] == '-' && arg[1] != '\0';
}

bool ParseCli(int argc, char** argv, CliOptions* opts) {
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    auto need_value = [&](const char* name) -> const char* {
      if (i + 1 >= argc) {
        std::cerr << name << " requires a value\n";
        return nullptr;
      }
      return argv[++i];
    };

    if (arg == "--help" || arg == "-h") {
      opts->show_help = true;
    } else if (arg == "--grid") {
      const char* value = need_value("--grid");
      if (!value) return false;
      opts->grid_selector = value;
      opts->has_grid = true;
    } else if (arg == "--color") {
      const char* value = need_value("--color");
      if (!value) return false;
      if (!ParseColorModeArg(value, &opts->color_mode)) {
        std::cerr << "Unknown color mode: " << value << "\n";
        return false;
      }
      opts->has_color = true;
    } else if (arg == "--display") {
      const char* value = need_value("--display");
      if (!value) return false;
      if (!ParseRenderModeArg(value, &opts->render_mode)) {
        std::cerr << "Unknown display mode: " << value << "\n";
        return false;
      }
      opts->has_render_mode = true;
    } else if (arg == "--gain") {
      const char* value = need_value("--gain");
      if (!value || !ParseFloatArg(value, &opts->density_gain)) {
        std::cerr << "Invalid --gain value\n";
        return false;
      }
      opts->has_gain = true;
    } else if (arg == "--window") {
      const char* value = need_value("--window");
      if (!value || !ParseRangeArg(value, &opts->window_min, &opts->window_max)) {
        std::cerr << "Invalid --window value. Use min:max\n";
        return false;
      }
      opts->has_window = true;
    } else if (arg == "--window-percentile") {
      const char* value = need_value("--window-percentile");
      if (!value || !ParseRangeArg(value, &opts->window_percentile_min,
                                   &opts->window_percentile_max)) {
        std::cerr << "Invalid --window-percentile value. Use lower:upper\n";
        return false;
      }
      opts->has_percentile_window = true;
    } else if (arg == "--gamma") {
      const char* value = need_value("--gamma");
      if (!value || !ParseFloatArg(value, &opts->value_gamma)) {
        std::cerr << "Invalid --gamma value\n";
        return false;
      }
      opts->has_gamma = true;
    } else if (arg == "--opacity-power") {
      const char* value = need_value("--opacity-power");
      if (!value || !ParseFloatArg(value, &opts->opacity_power)) {
        std::cerr << "Invalid --opacity-power value\n";
        return false;
      }
      opts->has_opacity_power = true;
    } else if (arg == "--invert") {
      opts->invert_values = true;
    } else if (arg == "--steps") {
      const char* value = need_value("--steps");
      if (!value || !ParseIntArg(value, &opts->sample_steps)) {
        std::cerr << "Invalid --steps value\n";
        return false;
      }
      opts->has_steps = true;
    } else if (arg == "--ray") {
      const char* value = need_value("--ray");
      if (!value || !ParseRayModeArg(value, &opts->ray_mode)) {
        std::cerr << "Invalid --ray value. Use composite, mip, or iso\n";
        return false;
      }
      opts->has_ray_mode = true;
    } else if (arg == "--iso") {
      const char* value = need_value("--iso");
      if (!value || !ParseFloatArg(value, &opts->iso_threshold)) {
        std::cerr << "Invalid --iso value\n";
        return false;
      }
      opts->has_iso_threshold = true;
    } else if (arg == "--pt-scale") {
      const char* value = need_value("--pt-scale");
      if (!value || !ParseIntArg(value, &opts->path_trace_scale)) {
        std::cerr << "Invalid --pt-scale value\n";
        return false;
      }
      opts->has_path_trace_scale = true;
    } else if (arg == "--pt-rows") {
      const char* value = need_value("--pt-rows");
      if (!value || !ParseIntArg(value, &opts->path_trace_rows_per_frame)) {
        std::cerr << "Invalid --pt-rows value\n";
        return false;
      }
      opts->has_path_trace_rows = true;
    } else if (arg == "--pt-depth") {
      const char* value = need_value("--pt-depth");
      if (!value || !ParseIntArg(value, &opts->path_trace_max_depth)) {
        std::cerr << "Invalid --pt-depth value\n";
        return false;
      }
      opts->has_path_trace_depth = true;
    } else if (arg == "--pt-backend") {
      const char* value = need_value("--pt-backend");
      if (!value) return false;
      const std::string backend = value;
      if (backend == "auto") {
        opts->path_trace_backend = 0;
      } else if (backend == "gpu" || backend == "compute") {
        opts->path_trace_backend = 1;
      } else if (backend == "cpu") {
        opts->path_trace_backend = 2;
      } else if (backend == "vulkan" || backend == "vk") {
        opts->path_trace_backend = 3;
      } else {
        std::cerr << "Invalid --pt-backend value. Use auto, gpu, vulkan, or cpu\n";
        return false;
      }
      opts->has_path_trace_backend = true;
    } else if (arg == "--pt-spp") {
      const char* value = need_value("--pt-spp");
      if (!value || !ParseIntArg(value, &opts->path_trace_capture_samples)) {
        std::cerr << "Invalid --pt-spp value\n";
        return false;
      }
      opts->has_path_trace_capture_samples = true;
    } else if (arg == "--sun") {
      const char* value = need_value("--sun");
      if (!value || !ParsePairArg(value, &opts->path_trace_sun_angle,
                                  &opts->path_trace_sun_azimuth)) {
        std::cerr << "Invalid --sun value. Use elevation:azimuth in degrees\n";
        return false;
      }
      opts->has_sun = true;
    } else if (arg == "--sun-strength") {
      const char* value = need_value("--sun-strength");
      if (!value || !ParseFloatArg(value, &opts->path_trace_sun_strength)) {
        std::cerr << "Invalid --sun-strength value\n";
        return false;
      }
      opts->has_sun_strength = true;
    } else if (arg == "--sky-strength") {
      const char* value = need_value("--sky-strength");
      if (!value || !ParseFloatArg(value, &opts->path_trace_sky_strength)) {
        std::cerr << "Invalid --sky-strength value\n";
        return false;
      }
      opts->has_sky_strength = true;
    } else if (arg == "--pt-albedo") {
      const char* value = need_value("--pt-albedo");
      if (!value || !ParseFloatArg(value, &opts->path_trace_albedo)) {
        std::cerr << "Invalid --pt-albedo value\n";
        return false;
      }
      opts->has_path_trace_albedo = true;
    } else if (arg == "--shade") {
      opts->shade_enabled = true;
      opts->has_shade_enabled = true;
    } else if (arg == "--no-shade") {
      opts->shade_enabled = false;
      opts->has_shade_enabled = true;
    } else if (arg == "--shade-strength") {
      const char* value = need_value("--shade-strength");
      if (!value || !ParseFloatArg(value, &opts->shade_strength)) {
        std::cerr << "Invalid --shade-strength value\n";
        return false;
      }
      opts->has_shade_strength = true;
    } else if (arg == "--light") {
      const char* value = need_value("--light");
      float light[3] = {};
      if (!value || !ParseVec3Csv(value, light)) {
        std::cerr << "Invalid --light value. Use x,y,z\n";
        return false;
      }
      opts->light_dir = Vec3{light[0], light[1], light[2]};
      opts->has_light_dir = true;
    } else if (arg == "--slice") {
      const char* value = need_value("--slice");
      if (!value || !ParseSliceArg(value, &opts->slice_axis, &opts->slice_pos,
                                   &opts->slice_thickness)) {
        std::cerr << "Invalid --slice value. Use x:0.5[:0.04], y:..., z:..., or off:0\n";
        return false;
      }
      opts->has_slice = true;
    } else if (arg == "--clip") {
      const char* value = need_value("--clip");
      if (!value || !ParseClipArg(value, opts->clip_min, opts->clip_max)) {
        std::cerr << "Invalid --clip value. Use minx,miny,minz:maxx,maxy,maxz\n";
        return false;
      }
      opts->has_clip = true;
    } else if (arg == "--clip-active") {
      opts->clip_active = true;
    } else if (arg == "--capture") {
      const char* value = need_value("--capture");
      if (!value) return false;
      opts->capture_path = value;
      opts->has_capture = true;
    } else if (arg == "--quit") {
      opts->quit_after_capture = true;
    } else if (arg == "--no-grid") {
      opts->no_grid = true;
    } else if (arg == "--sdf-fog") {
      opts->sdf_fog_mode = true;
    } else if (arg == "--no-internal-boxes") {
      opts->hide_internal_boxes = true;
    } else if (arg == "--no-leaf-boxes") {
      opts->hide_leaf_boxes = true;
    } else if (arg == "--no-dense-bounds") {
      opts->hide_dense_bounds = true;
    } else if (arg == "--hide-hud") {
      opts->hide_hud = true;
    } else if (arg == "--hide-panel") {
      opts->hide_panel = true;
    } else if (arg == "--camera") {
      const char* value = need_value("--camera");
      if (!value || !ParseCameraArg(value, &opts->camera_longitude,
                                    &opts->camera_latitude, &opts->camera_distance,
                                    &opts->camera_target)) {
        std::cerr << "Invalid --camera value. Use lon,lat,distance:targetx,targety,targetz\n";
        return false;
      }
      opts->has_camera = true;
    } else if (arg == "--size") {
      const char* value = need_value("--size");
      if (!value || !ParseWindowSizeArg(value, &opts->window_width, &opts->window_height)) {
        std::cerr << "Invalid --size value. Use WIDTHxHEIGHT\n";
        return false;
      }
      opts->has_window_size = true;
    } else if (IsOption(arg.c_str())) {
      std::cerr << "Unknown option: " << arg << "\n";
      return false;
    } else if (opts->input_path.empty()) {
      opts->input_path = arg;
    } else {
      std::cerr << "Unexpected positional argument: " << arg << "\n";
      return false;
    }
  }
  return true;
}

void PrintUsage(const char* argv0) {
  std::cout
      << "Usage: " << argv0 << " [options] [file.vdb]\n"
      << "\n"
      << "Options:\n"
      << "  --grid <index|name>                Select grid/attribute\n"
      << "  --display volume|volume+grid|grid  Set display mode\n"
      << "  --color density|jet|blackbody|vector\n"
      << "  --gain <value>                     Set density gain\n"
      << "  --window <min:max>                 Set manual value window\n"
      << "  --window-percentile <lo:hi>        Window by value percentiles\n"
      << "  --gamma <value>                    Set value gamma\n"
      << "  --opacity-power <value>            Set opacity shaping power\n"
      << "  --invert                           Invert normalized values\n"
      << "  --steps <1..512>                   Set ray-march sample count\n"
      << "  --ray composite|mip|iso|pathtrace  Set ray projection mode\n"
      << "  --iso <0..1>                       Set normalized iso threshold\n"
      << "  --pt-scale <n>                     CPU path trace resolution divisor\n"
      << "  --pt-rows <n>                      CPU path trace rows per frame\n"
      << "  --pt-depth <n>                     CPU path trace scattering depth\n"
      << "  --pt-backend auto|gpu|vulkan|cpu   Progressive path trace backend\n"
      << "  --pt-spp <n>                       Wait for path trace passes before capture\n"
      << "  --sun <elevation:azimuth>          Sunsky angles in degrees\n"
      << "  --sun-strength <value>             Sun radiance scale\n"
      << "  --sky-strength <value>             Sky radiance scale\n"
      << "  --pt-albedo <0..1>                 Volume scattering albedo\n"
      << "  --shade / --no-shade               Enable or disable gradient shading\n"
      << "  --shade-strength <0..1>            Set shading strength\n"
      << "  --light <x,y,z>                    Set shading light direction\n"
      << "  --slice <axis:pos[:thickness]>     Example: --slice z:0.5:0.03\n"
      << "  --clip <minx,miny,minz:maxx,maxy,maxz>\n"
      << "  --clip-active                      Clip to non-background dense cells\n"
      << "  --capture <out.png>                Save first rendered frame\n"
      << "  --quit                             Exit after --capture\n"
      << "  --no-grid                          Start in volume-only mode\n"
      << "  --sdf-fog                          Interpret selected grid as SDF fog\n"
      << "  --no-internal-boxes                Hide internal-node boxes\n"
      << "  --no-leaf-boxes                    Hide leaf-node boxes\n"
      << "  --no-dense-bounds                  Hide dense-grid bounds\n"
      << "  --hide-hud                         Hide overlay HUD\n"
      << "  --hide-panel                       Hide ImGui control panel\n"
      << "  --camera <lon,lat,dist:tx,ty,tz>   Restore orbit camera\n"
      << "  --size <WIDTHxHEIGHT>              Set initial window size\n"
      << "  -h, --help                         Show this help\n"
      << "\n";
  PrintControls();
}

bool CheckShader(GLuint shader, const char* label) {
  GLint ok = 0;
  glGetShaderiv(shader, GL_COMPILE_STATUS, &ok);
  if (ok) return true;
  char log[4096];
  GLsizei len = 0;
  glGetShaderInfoLog(shader, sizeof(log), &len, log);
  std::cerr << label << " shader compile failed:\n" << log << "\n";
  return false;
}

GLuint CreateProgram(const char* vs, const char* fs) {
  GLuint vert = glCreateShader(GL_VERTEX_SHADER);
  glShaderSource(vert, 1, &vs, nullptr);
  glCompileShader(vert);
  if (!CheckShader(vert, "vertex")) {
    glDeleteShader(vert);
    return 0;
  }

  GLuint frag = glCreateShader(GL_FRAGMENT_SHADER);
  glShaderSource(frag, 1, &fs, nullptr);
  glCompileShader(frag);
  if (!CheckShader(frag, "fragment")) {
    glDeleteShader(vert);
    glDeleteShader(frag);
    return 0;
  }

  GLuint prog = glCreateProgram();
  glAttachShader(prog, vert);
  glAttachShader(prog, frag);
  glLinkProgram(prog);
  glDeleteShader(vert);
  glDeleteShader(frag);

  GLint ok = 0;
  glGetProgramiv(prog, GL_LINK_STATUS, &ok);
  if (!ok) {
    char log[4096];
    GLsizei len = 0;
    glGetProgramInfoLog(prog, sizeof(log), &len, log);
    std::cerr << "program link failed:\n" << log << "\n";
    glDeleteProgram(prog);
    return 0;
  }
  return prog;
}

GLuint CreateComputeProgram(const char* cs) {
  GLuint shader = glCreateShader(GL_COMPUTE_SHADER);
  glShaderSource(shader, 1, &cs, nullptr);
  glCompileShader(shader);
  if (!CheckShader(shader, "compute")) {
    glDeleteShader(shader);
    return 0;
  }
  GLuint prog = glCreateProgram();
  glAttachShader(prog, shader);
  glLinkProgram(prog);
  glDeleteShader(shader);
  GLint ok = 0;
  glGetProgramiv(prog, GL_LINK_STATUS, &ok);
  if (!ok) {
    char log[4096];
    GLsizei len = 0;
    glGetProgramInfoLog(prog, sizeof(log), &len, log);
    std::cerr << "compute program link failed:\n" << log << "\n";
    glDeleteProgram(prog);
    return 0;
  }
  return prog;
}

void SetMat4(GLuint program, const char* name, const Mat4& m) {
  glUniformMatrix4fv(glGetUniformLocation(program, name), 1, GL_FALSE, m.m);
}

void ComputeChildDims(const tvdb_grid_layout_t* layout, int child_dims[TVDB_MAX_TREE_DEPTH]) {
  for (int level = 0; level < layout->num_levels; ++level) {
    int dim = 1;
    for (int j = level + 1; j < layout->num_levels; ++j) {
      dim *= (1 << layout->levels[j].log2dim);
    }
    child_dims[level] = dim;
  }
}

void PopulateVdbNodeOrigins(tvdb_tree_t* tree, const int child_dims[TVDB_MAX_TREE_DEPTH]) {
  if (!tree || tree->num_nodes == 0) return;
  if (tree->nodes[0].type != TVDB_NODE_ROOT) return;
  const tvdb_grid_layout_t* layout = &tree->layout;

  struct Entry {
    std::size_t idx;
    int level;
    int ox;
    int oy;
    int oz;
  };

  std::vector<Entry> stack;
  const tvdb_root_node_t& root = tree->nodes[0].u.root;
  for (uint32_t i = 0; i < root.num_children; ++i) {
    stack.push_back(Entry{root.child_indices[i], 1,
                          root.child_origins[3 * i + 0],
                          root.child_origins[3 * i + 1],
                          root.child_origins[3 * i + 2]});
  }

  while (!stack.empty()) {
    const Entry e = stack.back();
    stack.pop_back();
    tvdb_tree_node_t& node = tree->nodes[e.idx];
    node.origin[0] = e.ox;
    node.origin[1] = e.oy;
    node.origin[2] = e.oz;
    if (node.type != TVDB_NODE_INTERNAL) continue;

    const tvdb_internal_node_t& in = node.u.internal;
    const int D = layout->levels[e.level].log2dim;
    const int mask_dim = 1 << D;
    const int child_span = child_dims[e.level];
    std::size_t child_n = 0;
    const int bitsize = in.child_mask.bitsize;
    for (int bit = 0; bit < bitsize; ++bit) {
      if (!tvdb_nodemask_is_on(&in.child_mask, bit)) continue;
      const int lx = (bit >> (2 * D)) & (mask_dim - 1);
      const int ly = (bit >> D) & (mask_dim - 1);
      const int lz = bit & (mask_dim - 1);
      stack.push_back(Entry{in.child_indices[child_n++], e.level + 1,
                            e.ox + lx * child_span,
                            e.oy + ly * child_span,
                            e.oz + lz * child_span});
    }
  }
}

bool DetectLevelSetGrid(const tvdb_grid_t* grid) {
  for (std::size_t i = 0; i < grid->metadata.count; ++i) {
    const tvdb_meta_entry_t* e = &grid->metadata.entries[i];
    if (!e->name || std::strcmp(e->name, "class") != 0) continue;
    if (e->value.type == TVDB_VALUE_STRING && e->value.u.s.str) {
      return std::strcmp(e->value.u.s.str, "level set") == 0;
    }
  }
  return false;
}

void CollectVdbNodeBoxes(const tvdb_grid_t* grid,
                         const int child_dims[TVDB_MAX_TREE_DEPTH],
                         VolumeData* out,
                         bool expand_bounds) {
  const tvdb_grid_layout_t* layout = &grid->tree.layout;
  const int leaf_level = layout->num_levels - 1;
  const int leaf_dim = 1 << layout->levels[leaf_level].log2dim;

  for (std::size_t i = 0; i < grid->tree.num_nodes; ++i) {
    const tvdb_tree_node_t* n = &grid->tree.nodes[i];
    if (n->type != TVDB_NODE_INTERNAL && n->type != TVDB_NODE_LEAF) continue;
    int span = 1;
    if (n->type == TVDB_NODE_LEAF) {
      span = leaf_dim;
    } else {
      span = child_dims[n->level] * (1 << layout->levels[n->level].log2dim);
    }

    VolumeNodeBox box;
    for (int a = 0; a < 3; ++a) {
      const float lo = n->origin[a] * out->voxel_size[a] + out->translation[a];
      const float hi = (n->origin[a] + span) * out->voxel_size[a] + out->translation[a];
      const float mn = std::min(lo, hi);
      const float mx = std::max(lo, hi);
      if (a == 0) {
        box.min.x = mn;
        box.max.x = mx;
      } else if (a == 1) {
        box.min.y = mn;
        box.max.y = mx;
      } else {
        box.min.z = mn;
        box.max.z = mx;
      }
    }
    box.level = n->level;
    out->max_level = std::max(out->max_level, box.level);
    out->node_boxes.push_back(box);
    if (expand_bounds) {
      out->world_bounds.expand(box.min);
      out->world_bounds.expand(box.max);
    }
  }
}

void ComputeVolumeStats(VolumeData* out) {
  if (!out || out->density.empty()) return;
  double sum = 0.0;
  std::size_t non_background = 0;
  float mn = std::numeric_limits<float>::infinity();
  float mx = -std::numeric_limits<float>::infinity();
  int active_min[3] = {out->dim[0], out->dim[1], out->dim[2]};
  int active_max[3] = {-1, -1, -1};
  for (int z = 0; z < out->dim[2]; ++z) {
    for (int y = 0; y < out->dim[1]; ++y) {
      for (int x = 0; x < out->dim[0]; ++x) {
        const std::size_t idx =
            static_cast<std::size_t>(x) +
            static_cast<std::size_t>(out->dim[0]) *
                (static_cast<std::size_t>(y) +
                 static_cast<std::size_t>(out->dim[1]) * static_cast<std::size_t>(z));
        const float v = out->density[idx];
        sum += static_cast<double>(v);
        mn = std::min(mn, v);
        mx = std::max(mx, v);
        if (std::fabs(v - out->background) > 1.0e-12f) {
          ++non_background;
          active_min[0] = std::min(active_min[0], x);
          active_min[1] = std::min(active_min[1], y);
          active_min[2] = std::min(active_min[2], z);
          active_max[0] = std::max(active_max[0], x);
          active_max[1] = std::max(active_max[1], y);
          active_max[2] = std::max(active_max[2], z);
        }
      }
    }
  }
  if (!std::isfinite(mn) || !std::isfinite(mx)) return;
  out->mean_value = static_cast<float>(sum / static_cast<double>(out->density.size()));
  out->non_background_fraction =
      static_cast<float>(static_cast<double>(non_background) /
                         static_cast<double>(out->density.size()));
  out->has_active_bbox = non_background > 0;
  if (out->has_active_bbox) {
    for (int axis = 0; axis < 3; ++axis) {
      out->active_index_min[axis] = active_min[axis];
      out->active_index_max[axis] = active_max[axis];
      out->active_uvw_min[axis] =
          static_cast<float>(active_min[axis]) / static_cast<float>(out->dim[axis]);
      out->active_uvw_max[axis] =
          static_cast<float>(active_max[axis] + 1) / static_cast<float>(out->dim[axis]);
    }
  }
  out->histogram_min = mn;
  out->histogram_max = mx;
  out->histogram.assign(kHistogramBins, 0.0f);
  const float range = mx - mn;
  if (range <= 1.0e-20f) {
    out->histogram[0] = 1.0f;
    return;
  }
  float max_count = 0.0f;
  for (float v : out->density) {
    int bin = static_cast<int>(((v - mn) / range) * static_cast<float>(kHistogramBins - 1));
    bin = std::max(0, std::min(kHistogramBins - 1, bin));
    out->histogram[bin] += 1.0f;
    max_count = std::max(max_count, out->histogram[bin]);
  }
  if (max_count > 0.0f) {
    for (float& v : out->histogram) v /= max_count;
  }
}

bool SplatVdbFloatGridInto(const tvdb_grid_t* grid, const int imin[3],
                           const int dim[3], int stride, float* dense,
                           float* min_val, float* max_val) {
  if (!grid || grid->tree.num_nodes == 0 || stride <= 0) return false;
  const tvdb_grid_layout_t* layout = &grid->tree.layout;
  if (layout->num_levels < 1) return false;
  const int leaf_level = layout->num_levels - 1;
  if (layout->levels[leaf_level].value_type != TVDB_VALUE_FLOAT) return false;
  const int leaf_log2 = layout->levels[leaf_level].log2dim;
  const int leaf_dim = 1 << leaf_log2;

  int child_dims[TVDB_MAX_TREE_DEPTH] = {};
  ComputeChildDims(layout, child_dims);
  PopulateVdbNodeOrigins(const_cast<tvdb_tree_t*>(&grid->tree), child_dims);

  auto splat = [&](int vlx, int vly, int vlz, int sx, int sy, int sz, float v) {
    if (sx <= 0 || sy <= 0 || sz <= 0) return;
    int ox_lo = vlx / stride;
    int oy_lo = vly / stride;
    int oz_lo = vlz / stride;
    int ox_hi = (vlx + sx - 1) / stride;
    int oy_hi = (vly + sy - 1) / stride;
    int oz_hi = (vlz + sz - 1) / stride;
    ox_lo = std::max(ox_lo, 0);
    oy_lo = std::max(oy_lo, 0);
    oz_lo = std::max(oz_lo, 0);
    ox_hi = std::min(ox_hi, dim[0] - 1);
    oy_hi = std::min(oy_hi, dim[1] - 1);
    oz_hi = std::min(oz_hi, dim[2] - 1);
    if (ox_lo > ox_hi || oy_lo > oy_hi || oz_lo > oz_hi) return;
    for (int oz = oz_lo; oz <= oz_hi; ++oz) {
      for (int oy = oy_lo; oy <= oy_hi; ++oy) {
        std::size_t row = static_cast<std::size_t>(ox_lo) +
                          static_cast<std::size_t>(dim[0]) *
                              (static_cast<std::size_t>(oy) +
                               static_cast<std::size_t>(dim[1]) *
                                   static_cast<std::size_t>(oz));
        for (int ox = ox_lo; ox <= ox_hi; ++ox, ++row) {
          dense[row] = v;
        }
      }
    }
    *min_val = std::min(*min_val, v);
    *max_val = std::max(*max_val, v);
  };

  for (std::size_t i = 0; i < grid->tree.num_nodes; ++i) {
    const tvdb_tree_node_t* n = &grid->tree.nodes[i];
    if (n->type != TVDB_NODE_INTERNAL) continue;
    const tvdb_internal_node_t* in = &n->u.internal;
    const int level = n->level;
    if (level <= 0 || level >= layout->num_levels) continue;
    if (layout->levels[level].value_type != TVDB_VALUE_FLOAT) continue;
    const int D = layout->levels[level].log2dim;
    const int mask_dim = 1 << D;
    const int bitsize = in->child_mask.bitsize;
    const int child_span = child_dims[level];
    if (child_span <= 0) continue;
    const std::size_t vsize = tvdb_value_type_size(TVDB_VALUE_FLOAT);
    if (in->values_size / vsize != static_cast<std::size_t>(bitsize)) continue;
    const float* tile_values = reinterpret_cast<const float*>(in->values);
    for (int bit = 0; bit < bitsize; ++bit) {
      if (tvdb_nodemask_is_on(&in->child_mask, bit)) continue;
      const int lx = (bit >> (2 * D)) & (mask_dim - 1);
      const int ly = (bit >> D) & (mask_dim - 1);
      const int lz = bit & (mask_dim - 1);
      const int vlx = (n->origin[0] + lx * child_span) - imin[0];
      const int vly = (n->origin[1] + ly * child_span) - imin[1];
      const int vlz = (n->origin[2] + lz * child_span) - imin[2];
      splat(vlx, vly, vlz, child_span, child_span, child_span, tile_values[bit]);
    }
  }

  for (std::size_t i = 0; i < grid->tree.num_nodes; ++i) {
    const tvdb_tree_node_t* n = &grid->tree.nodes[i];
    if (n->type != TVDB_NODE_LEAF) continue;
    const tvdb_leaf_node_t* leaf = &n->u.leaf;
    const float* voxels = reinterpret_cast<const float*>(leaf->data);
    if (!voxels) continue;
    const int ox = n->origin[0] - imin[0];
    const int oy = n->origin[1] - imin[1];
    const int oz = n->origin[2] - imin[2];
    for (int lx = 0; lx < leaf_dim; ++lx) {
      for (int ly = 0; ly < leaf_dim; ++ly) {
        for (int lz = 0; lz < leaf_dim; ++lz) {
          const int li = (lx << (2 * leaf_log2)) | (ly << leaf_log2) | lz;
          if (!tvdb_nodemask_is_on(&leaf->value_mask, li)) continue;
          splat(ox + lx, oy + ly, oz + lz, 1, 1, 1, voxels[li]);
        }
      }
    }
  }
  return true;
}

bool SplatVdbVec3GridInto(const tvdb_grid_t* grid, const int imin[3],
                          const int dim[3], int stride, float* dense,
                          float* max_len) {
  if (!grid || grid->tree.num_nodes == 0 || stride <= 0) return false;
  const tvdb_grid_layout_t* layout = &grid->tree.layout;
  if (layout->num_levels < 1) return false;
  const int leaf_level = layout->num_levels - 1;
  if (layout->levels[leaf_level].value_type != TVDB_VALUE_VEC3F) return false;
  const int leaf_log2 = layout->levels[leaf_level].log2dim;
  const int leaf_dim = 1 << leaf_log2;

  int child_dims[TVDB_MAX_TREE_DEPTH] = {};
  ComputeChildDims(layout, child_dims);
  PopulateVdbNodeOrigins(const_cast<tvdb_tree_t*>(&grid->tree), child_dims);

  auto write_cell = [&](int ox, int oy, int oz, float vx, float vy, float vz) {
    const std::size_t idx =
        (static_cast<std::size_t>(ox) +
         static_cast<std::size_t>(dim[0]) *
             (static_cast<std::size_t>(oy) +
              static_cast<std::size_t>(dim[1]) *
                  static_cast<std::size_t>(oz))) * 3;
    dense[idx + 0] = vx;
    dense[idx + 1] = vy;
    dense[idx + 2] = vz;
    *max_len = std::max(*max_len, std::sqrt(vx * vx + vy * vy + vz * vz));
  };

  auto splat = [&](int vlx, int vly, int vlz, int sx, int sy, int sz,
                   float vx, float vy, float vz) {
    if (sx <= 0 || sy <= 0 || sz <= 0) return;
    int ox_lo = std::max(vlx / stride, 0);
    int oy_lo = std::max(vly / stride, 0);
    int oz_lo = std::max(vlz / stride, 0);
    int ox_hi = std::min((vlx + sx - 1) / stride, dim[0] - 1);
    int oy_hi = std::min((vly + sy - 1) / stride, dim[1] - 1);
    int oz_hi = std::min((vlz + sz - 1) / stride, dim[2] - 1);
    if (ox_lo > ox_hi || oy_lo > oy_hi || oz_lo > oz_hi) return;
    for (int oz = oz_lo; oz <= oz_hi; ++oz) {
      for (int oy = oy_lo; oy <= oy_hi; ++oy) {
        for (int ox = ox_lo; ox <= ox_hi; ++ox) {
          write_cell(ox, oy, oz, vx, vy, vz);
        }
      }
    }
  };

  for (std::size_t i = 0; i < grid->tree.num_nodes; ++i) {
    const tvdb_tree_node_t* n = &grid->tree.nodes[i];
    if (n->type != TVDB_NODE_INTERNAL) continue;
    const tvdb_internal_node_t* in = &n->u.internal;
    const int level = n->level;
    if (level <= 0 || level >= layout->num_levels) continue;
    if (layout->levels[level].value_type != TVDB_VALUE_VEC3F) continue;
    const int D = layout->levels[level].log2dim;
    const int mask_dim = 1 << D;
    const int bitsize = in->child_mask.bitsize;
    const int child_span = child_dims[level];
    if (child_span <= 0) continue;
    const std::size_t vsize = tvdb_value_type_size(TVDB_VALUE_VEC3F);
    if (in->values_size / vsize != static_cast<std::size_t>(bitsize)) continue;
    const float* tile_values = reinterpret_cast<const float*>(in->values);
    for (int bit = 0; bit < bitsize; ++bit) {
      if (tvdb_nodemask_is_on(&in->child_mask, bit)) continue;
      const int lx = (bit >> (2 * D)) & (mask_dim - 1);
      const int ly = (bit >> D) & (mask_dim - 1);
      const int lz = bit & (mask_dim - 1);
      const int vlx = (n->origin[0] + lx * child_span) - imin[0];
      const int vly = (n->origin[1] + ly * child_span) - imin[1];
      const int vlz = (n->origin[2] + lz * child_span) - imin[2];
      splat(vlx, vly, vlz, child_span, child_span, child_span,
            tile_values[bit * 3 + 0],
            tile_values[bit * 3 + 1],
            tile_values[bit * 3 + 2]);
    }
  }

  for (std::size_t i = 0; i < grid->tree.num_nodes; ++i) {
    const tvdb_tree_node_t* n = &grid->tree.nodes[i];
    if (n->type != TVDB_NODE_LEAF) continue;
    const tvdb_leaf_node_t* leaf = &n->u.leaf;
    const float* voxels = reinterpret_cast<const float*>(leaf->data);
    if (!voxels) continue;
    const int ox = n->origin[0] - imin[0];
    const int oy = n->origin[1] - imin[1];
    const int oz = n->origin[2] - imin[2];
    for (int lx = 0; lx < leaf_dim; ++lx) {
      for (int ly = 0; ly < leaf_dim; ++ly) {
        for (int lz = 0; lz < leaf_dim; ++lz) {
          const int li = (lx << (2 * leaf_log2)) | (ly << leaf_log2) | lz;
          if (!tvdb_nodemask_is_on(&leaf->value_mask, li)) continue;
          splat(ox + lx, oy + ly, oz + lz, 1, 1, 1,
                voxels[li * 3 + 0], voxels[li * 3 + 1], voxels[li * 3 + 2]);
        }
      }
    }
  }
  return true;
}

bool ExtractVdbFloatVolume(const tvdb_grid_t* grid, VolumeData* out) {
  if (!grid || grid->tree.num_nodes == 0) return false;
  const tvdb_grid_layout_t* layout = &grid->tree.layout;
  const int num_levels = layout->num_levels;
  if (num_levels < 1) return false;
  const int leaf_level = num_levels - 1;
  if (layout->levels[leaf_level].value_type != TVDB_VALUE_FLOAT) return false;
  const int leaf_log2 = layout->levels[leaf_level].log2dim;
  const int leaf_dim = 1 << leaf_log2;

  int child_dims[TVDB_MAX_TREE_DEPTH] = {};
  ComputeChildDims(layout, child_dims);
  PopulateVdbNodeOrigins(const_cast<tvdb_tree_t*>(&grid->tree), child_dims);

  int imin[3] = {std::numeric_limits<int>::max(), std::numeric_limits<int>::max(),
                 std::numeric_limits<int>::max()};
  int imax[3] = {std::numeric_limits<int>::min(), std::numeric_limits<int>::min(),
                 std::numeric_limits<int>::min()};
  std::size_t leaf_count = 0;
  for (std::size_t i = 0; i < grid->tree.num_nodes; ++i) {
    const tvdb_tree_node_t* n = &grid->tree.nodes[i];
    if (n->type != TVDB_NODE_LEAF) continue;
    ++leaf_count;
    for (int a = 0; a < 3; ++a) {
      imin[a] = std::min(imin[a], n->origin[a]);
      imax[a] = std::max(imax[a], n->origin[a] + leaf_dim);
    }
  }
  if (leaf_count == 0) return false;

  const int native_dim[3] = {imax[0] - imin[0], imax[1] - imin[1], imax[2] - imin[2]};
  if (native_dim[0] <= 0 || native_dim[1] <= 0 || native_dim[2] <= 0) return false;

  int stride = 1;
  while (true) {
    const std::size_t ox = static_cast<std::size_t>((native_dim[0] + stride - 1) / stride);
    const std::size_t oy = static_cast<std::size_t>((native_dim[1] + stride - 1) / stride);
    const std::size_t oz = static_cast<std::size_t>((native_dim[2] + stride - 1) / stride);
    if (ox * oy * oz <= kMaxDenseVoxels) break;
    ++stride;
    if (stride > 64) return false;
  }

  out->dim[0] = (native_dim[0] + stride - 1) / stride;
  out->dim[1] = (native_dim[1] + stride - 1) / stride;
  out->dim[2] = (native_dim[2] + stride - 1) / stride;
  const std::size_t voxel_count =
      static_cast<std::size_t>(out->dim[0]) *
      static_cast<std::size_t>(out->dim[1]) *
      static_cast<std::size_t>(out->dim[2]);
  if (voxel_count == 0) return false;

  out->origin_index[0] = imin[0];
  out->origin_index[1] = imin[1];
  out->origin_index[2] = imin[2];
  for (int a = 0; a < 3; ++a) {
    out->voxel_size[a] =
        grid->transform.voxel_size[a] != 0.0
            ? static_cast<float>(grid->transform.voxel_size[a])
            : 1.0f;
    out->translation[a] = static_cast<float>(grid->transform.translation[a]);
  }
  out->is_level_set = DetectLevelSetGrid(grid);

  float background = 0.0f;
  if (grid->tree.nodes[0].type == TVDB_NODE_ROOT &&
      grid->tree.nodes[0].u.root.background.type == TVDB_VALUE_FLOAT) {
    background = grid->tree.nodes[0].u.root.background.u.f;
  }
  out->density.assign(voxel_count, background);

  float min_val = std::numeric_limits<float>::infinity();
  float max_val = -std::numeric_limits<float>::infinity();
  if (!SplatVdbFloatGridInto(grid, imin, out->dim, stride,
                             out->density.data(), &min_val, &max_val)) {
    return false;
  }
  if (!std::isfinite(min_val)) {
    min_val = background;
    max_val = background + 1.0f;
  }
  out->min_value = min_val;
  out->max_value = max_val;
  out->background = background;
  out->downsample_stride = stride;
  ComputeVolumeStats(out);

  out->world_bounds.expand(Vec3{
      imin[0] * out->voxel_size[0] + out->translation[0],
      imin[1] * out->voxel_size[1] + out->translation[1],
      imin[2] * out->voxel_size[2] + out->translation[2]});
  out->world_bounds.expand(Vec3{
      imax[0] * out->voxel_size[0] + out->translation[0],
      imax[1] * out->voxel_size[1] + out->translation[1],
      imax[2] * out->voxel_size[2] + out->translation[2]});

  CollectVdbNodeBoxes(grid, child_dims, out, false);
  return true;
}

bool ExtractVdbTopologyOnly(const tvdb_grid_t* grid, VolumeData* out) {
  if (!grid || grid->tree.num_nodes == 0) return false;
  const tvdb_grid_layout_t* layout = &grid->tree.layout;
  if (layout->num_levels < 1) return false;
  int child_dims[TVDB_MAX_TREE_DEPTH] = {};
  ComputeChildDims(layout, child_dims);
  PopulateVdbNodeOrigins(const_cast<tvdb_tree_t*>(&grid->tree), child_dims);

  for (int a = 0; a < 3; ++a) {
    out->voxel_size[a] =
        grid->transform.voxel_size[a] != 0.0
            ? static_cast<float>(grid->transform.voxel_size[a])
            : 1.0f;
    out->translation[a] = static_cast<float>(grid->transform.translation[a]);
  }

  const int leaf_level = layout->num_levels - 1;
  const int leaf_dim = 1 << layout->levels[leaf_level].log2dim;
  bool have_leaf = false;
  int imin[3] = {std::numeric_limits<int>::max(), std::numeric_limits<int>::max(),
                 std::numeric_limits<int>::max()};
  int imax[3] = {std::numeric_limits<int>::min(), std::numeric_limits<int>::min(),
                 std::numeric_limits<int>::min()};
  for (std::size_t i = 0; i < grid->tree.num_nodes; ++i) {
    const tvdb_tree_node_t* n = &grid->tree.nodes[i];
    if (n->type != TVDB_NODE_LEAF) continue;
    have_leaf = true;
    for (int a = 0; a < 3; ++a) {
      imin[a] = std::min(imin[a], n->origin[a]);
      imax[a] = std::max(imax[a], n->origin[a] + leaf_dim);
    }
  }
  if (have_leaf) {
    out->world_bounds.expand(Vec3{
        imin[0] * out->voxel_size[0] + out->translation[0],
        imin[1] * out->voxel_size[1] + out->translation[1],
        imin[2] * out->voxel_size[2] + out->translation[2]});
    out->world_bounds.expand(Vec3{
        imax[0] * out->voxel_size[0] + out->translation[0],
        imax[1] * out->voxel_size[1] + out->translation[1],
        imax[2] * out->voxel_size[2] + out->translation[2]});
  }
  CollectVdbNodeBoxes(grid, child_dims, out, false);
  return !out->node_boxes.empty();
}

bool IsFloatGrid(const tvdb_grid_t& grid) {
  return grid.tree.layout.num_levels >= 1 &&
         grid.tree.layout.levels[grid.tree.layout.num_levels - 1].value_type ==
             TVDB_VALUE_FLOAT;
}

bool IsVec3Grid(const tvdb_grid_t& grid) {
  return grid.tree.layout.num_levels >= 1 &&
         grid.tree.layout.levels[grid.tree.layout.num_levels - 1].value_type ==
             TVDB_VALUE_VEC3F;
}

bool GridNameContains(const tvdb_grid_t& grid, const char* needle) {
  return grid.descriptor.grid_name && std::strstr(grid.descriptor.grid_name, needle) != nullptr;
}

bool VoxelSizeMatches(const tvdb_grid_t& grid, const VolumeData& volume) {
  for (int a = 0; a < 3; ++a) {
    const float vs =
        grid.transform.voxel_size[a] != 0.0
            ? static_cast<float>(grid.transform.voxel_size[a])
            : 1.0f;
    if (std::fabs(vs - volume.voxel_size[a]) > 1.0e-4f) return false;
  }
  return true;
}

bool LoadVdbScene(const std::string& filepath, SceneData* scene, std::string* error) {
  tvdb_file_t file;
  tvdb_error_t err;
  std::memset(&file, 0, sizeof(file));
  std::memset(&err, 0, sizeof(err));
  const tvdb_status_t st = tvdb_file_open(&file, filepath.c_str(), nullptr, &err);
  if (st != TVDB_OK) {
    if (error) *error = err.message[0] ? err.message : tvdb_status_string(st);
    return false;
  }

  if (tvdb_read_all_grids(&file, &err) != TVDB_OK) {
    if (error) *error = err.message[0] ? err.message : "Failed to read VDB grids.";
    tvdb_file_close(&file);
    return false;
  }

  std::size_t primary_grid = file.num_grids;
  for (std::size_t i = 0; i < file.num_grids; ++i) {
    if (IsFloatGrid(file.grids[i]) && GridNameContains(file.grids[i], "density")) {
      primary_grid = i;
      break;
    }
  }
  if (primary_grid == file.num_grids) {
    for (std::size_t i = 0; i < file.num_grids; ++i) {
      if (IsFloatGrid(file.grids[i])) {
        primary_grid = i;
        break;
      }
    }
  }

  std::vector<bool> handled(file.num_grids, false);
  if (primary_grid != file.num_grids) {
    const tvdb_grid_t& grid = file.grids[primary_grid];
    VolumeData volume;
    volume.name = grid.descriptor.grid_name
                      ? grid.descriptor.grid_name
                      : ("grid_" + std::to_string(primary_grid));
    if (ExtractVdbFloatVolume(&grid, &volume)) {
      handled[primary_grid] = true;

      for (std::size_t j = 0; j < file.num_grids; ++j) {
        if (j == primary_grid || handled[j]) continue;
        const tvdb_grid_t& extra = file.grids[j];
        if (!IsFloatGrid(extra) || !VoxelSizeMatches(extra, volume)) continue;
        const std::size_t voxel_count =
            static_cast<std::size_t>(volume.dim[0]) *
            static_cast<std::size_t>(volume.dim[1]) *
            static_cast<std::size_t>(volume.dim[2]);
        float bg = 0.0f;
        if (extra.tree.num_nodes > 0 && extra.tree.nodes[0].type == TVDB_NODE_ROOT &&
            extra.tree.nodes[0].u.root.background.type == TVDB_VALUE_FLOAT) {
          bg = extra.tree.nodes[0].u.root.background.u.f;
        }
        volume.emission.assign(voxel_count, bg);
        volume.emission_background = bg;
        volume.emission_name = extra.descriptor.grid_name ? extra.descriptor.grid_name : "";
        float emin = std::numeric_limits<float>::infinity();
        float emax = -std::numeric_limits<float>::infinity();
        const int imin[3] = {volume.origin_index[0], volume.origin_index[1],
                             volume.origin_index[2]};
        if (SplatVdbFloatGridInto(&extra, imin, volume.dim, volume.downsample_stride,
                                  volume.emission.data(), &emin, &emax)) {
          if (!std::isfinite(emin)) {
            emin = bg;
            emax = bg + 1.0f;
          }
          volume.emission_min = emin;
          volume.emission_max = emax;
          scene->notes.push_back("emission: " + volume.emission_name);
          break;
        }
        volume.emission.clear();
        volume.emission_name.clear();
      }

      for (std::size_t j = 0; j < file.num_grids; ++j) {
        if (j == primary_grid || handled[j]) continue;
        const tvdb_grid_t& extra = file.grids[j];
        if (!IsVec3Grid(extra) || !VoxelSizeMatches(extra, volume)) continue;
        const std::size_t voxel_count =
            static_cast<std::size_t>(volume.dim[0]) *
            static_cast<std::size_t>(volume.dim[1]) *
            static_cast<std::size_t>(volume.dim[2]);
        volume.vector3.assign(voxel_count * 3, 0.0f);
        volume.vector_name = extra.descriptor.grid_name ? extra.descriptor.grid_name : "";
        const int imin[3] = {volume.origin_index[0], volume.origin_index[1],
                             volume.origin_index[2]};
        float vmax = 0.0f;
        if (SplatVdbVec3GridInto(&extra, imin, volume.dim, volume.downsample_stride,
                                 volume.vector3.data(), &vmax)) {
          volume.vector_max_len = vmax;
          handled[j] = true;
          scene->notes.push_back("vector: " + volume.vector_name);
          break;
        }
        volume.vector3.clear();
        volume.vector_name.clear();
      }

      scene->bounds.expand(volume.world_bounds);
      scene->notes.push_back("volume: " + volume.name + " dim=" +
                             std::to_string(volume.dim[0]) + "x" +
                             std::to_string(volume.dim[1]) + "x" +
                             std::to_string(volume.dim[2]) +
                             " stride=" + std::to_string(volume.downsample_stride));
      scene->volumes.push_back(std::move(volume));
    }
  }

  for (std::size_t i = 0; i < file.num_grids; ++i) {
    if (handled[i]) continue;
    const tvdb_grid_t& grid = file.grids[i];
    VolumeData volume;
    volume.name = grid.descriptor.grid_name ? grid.descriptor.grid_name
                                            : ("grid_" + std::to_string(i));
    if (ExtractVdbFloatVolume(&grid, &volume)) {
      scene->bounds.expand(volume.world_bounds);
      scene->notes.push_back("volume: " + volume.name);
      scene->volumes.push_back(std::move(volume));
      continue;
    }
    if (ExtractVdbTopologyOnly(&grid, &volume)) {
      scene->bounds.expand(volume.world_bounds);
      scene->notes.push_back("topology: " + volume.name +
                             " boxes=" + std::to_string(volume.node_boxes.size()));
      scene->volumes.push_back(std::move(volume));
    }
  }

  tvdb_file_close(&file);
  if (scene->volumes.empty()) {
    if (error) *error = "No displayable VDB grids found.";
    return false;
  }
  return true;
}

LineMesh UploadLineMesh(const std::vector<float>& vertices, const std::vector<uint32_t>& indices) {
  LineMesh mesh;
  if (vertices.empty() || indices.empty()) return mesh;
  glGenVertexArrays(1, &mesh.vao);
  glGenBuffers(1, &mesh.vbo);
  glGenBuffers(1, &mesh.ebo);
  glBindVertexArray(mesh.vao);
  glBindBuffer(GL_ARRAY_BUFFER, mesh.vbo);
  glBufferData(GL_ARRAY_BUFFER, vertices.size() * sizeof(float),
               vertices.data(), GL_STATIC_DRAW);
  glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, mesh.ebo);
  glBufferData(GL_ELEMENT_ARRAY_BUFFER, indices.size() * sizeof(uint32_t),
               indices.data(), GL_STATIC_DRAW);
  glVertexAttribPointer(0, 3, GL_FLOAT, GL_FALSE, 6 * sizeof(float), nullptr);
  glEnableVertexAttribArray(0);
  glVertexAttribPointer(1, 3, GL_FLOAT, GL_FALSE, 6 * sizeof(float),
                        reinterpret_cast<void*>(3 * sizeof(float)));
  glEnableVertexAttribArray(1);
  glBindVertexArray(0);
  mesh.index_count = static_cast<GLsizei>(indices.size());
  return mesh;
}

void AppendLineBox(const Vec3& mn, const Vec3& mx, const Vec3& color,
                   std::vector<float>* vertices, std::vector<uint32_t>* indices) {
  static const uint32_t edge_offsets[24] = {
      0, 1, 1, 2, 2, 3, 3, 0,
      4, 5, 5, 6, 6, 7, 7, 4,
      0, 4, 1, 5, 2, 6, 3, 7};
  const Vec3 corners[8] = {
      {mn.x, mn.y, mn.z}, {mx.x, mn.y, mn.z}, {mx.x, mx.y, mn.z}, {mn.x, mx.y, mn.z},
      {mn.x, mn.y, mx.z}, {mx.x, mn.y, mx.z}, {mx.x, mx.y, mx.z}, {mn.x, mx.y, mx.z}};
  const uint32_t base = static_cast<uint32_t>(vertices->size() / 6);
  for (int c = 0; c < 8; ++c) {
    vertices->push_back(corners[c].x);
    vertices->push_back(corners[c].y);
    vertices->push_back(corners[c].z);
    vertices->push_back(color.x);
    vertices->push_back(color.y);
    vertices->push_back(color.z);
  }
  for (int e = 0; e < 24; ++e) indices->push_back(base + edge_offsets[e]);
}

LineMesh BuildVolumeNodeLineMesh(const VolumeData& volume, bool leaves) {
  std::vector<float> vertices;
  std::vector<uint32_t> indices;
  vertices.reserve(volume.node_boxes.size() * 8 * 6);
  indices.reserve(volume.node_boxes.size() * 24);
  const int max_level = std::max(volume.max_level, 1);

  for (std::size_t b = 0; b < volume.node_boxes.size(); ++b) {
    const VolumeNodeBox& box = volume.node_boxes[b];
    const bool is_leaf = box.level >= volume.max_level;
    if (is_leaf != leaves) continue;
    const float t = static_cast<float>(box.level) / static_cast<float>(max_level);
    const Vec3 color{1.0f - t, 0.2f + 0.8f * t, 0.25f + 0.6f * (1.0f - t)};
    AppendLineBox(box.min, box.max, color, &vertices, &indices);
  }
  return UploadLineMesh(vertices, indices);
}

LineMesh BuildDenseBoundsLineMesh(const VolumeData& volume) {
  if (!volume.world_bounds.valid) return LineMesh{};
  std::vector<float> vertices;
  std::vector<uint32_t> indices;
  AppendLineBox(volume.world_bounds.min, volume.world_bounds.max,
                Vec3{0.95f, 0.95f, 1.0f}, &vertices, &indices);
  return UploadLineMesh(vertices, indices);
}

LineMesh BuildSliceLineMesh(const Bounds& bounds, int axis, float pos) {
  if (!bounds.valid || axis <= 0) return LineMesh{};
  const Vec3 mn = bounds.min;
  const Vec3 mx = bounds.max;
  Vec3 p[4];
  if (axis == 1) {
    const float x = mn.x + (mx.x - mn.x) * pos;
    p[0] = {x, mn.y, mn.z}; p[1] = {x, mx.y, mn.z}; p[2] = {x, mx.y, mx.z}; p[3] = {x, mn.y, mx.z};
  } else if (axis == 2) {
    const float y = mn.y + (mx.y - mn.y) * pos;
    p[0] = {mn.x, y, mn.z}; p[1] = {mx.x, y, mn.z}; p[2] = {mx.x, y, mx.z}; p[3] = {mn.x, y, mx.z};
  } else {
    const float z = mn.z + (mx.z - mn.z) * pos;
    p[0] = {mn.x, mn.y, z}; p[1] = {mx.x, mn.y, z}; p[2] = {mx.x, mx.y, z}; p[3] = {mn.x, mx.y, z};
  }
  std::vector<float> vertices;
  std::vector<uint32_t> indices = {0, 1, 1, 2, 2, 3, 3, 0};
  const Vec3 color{1.0f, 0.85f, 0.2f};
  for (int i = 0; i < 4; ++i) {
    vertices.push_back(p[i].x);
    vertices.push_back(p[i].y);
    vertices.push_back(p[i].z);
    vertices.push_back(color.x);
    vertices.push_back(color.y);
    vertices.push_back(color.z);
  }
  return UploadLineMesh(vertices, indices);
}

void UploadFloatTexture3D(GLuint* tex, int dim[3], const float* data) {
  glGenTextures(1, tex);
  glBindTexture(GL_TEXTURE_3D, *tex);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_R, GL_CLAMP_TO_EDGE);
  glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
  glTexImage3D(GL_TEXTURE_3D, 0, GL_R32F, dim[0], dim[1], dim[2], 0,
               GL_RED, GL_FLOAT, data);
  glBindTexture(GL_TEXTURE_3D, 0);
}

GpuVolume UploadVolume(const VolumeData& volume) {
  GpuVolume gpu;
  gpu.world_bounds = volume.world_bounds;
  gpu.has_density = !volume.density.empty() &&
                    volume.dim[0] > 0 && volume.dim[1] > 0 && volume.dim[2] > 0;
  gpu.is_level_set = volume.is_level_set;

  const float range = volume.max_value - volume.min_value;
  if (volume.is_level_set) {
    gpu.value_offset = volume.max_value;
    gpu.value_scale = range > 1.0e-6f ? -1.0f / range : -1.0f;
  } else {
    gpu.value_offset = volume.min_value;
    gpu.value_scale = range > 1.0e-6f ? 1.0f / range : 1.0f;
  }
  const float band_world = std::abs(volume.min_value);
  gpu.sdf_band_scale = band_world > 1.0e-6f ? 1.0f / band_world : 1.0f;

  if (gpu.has_density) {
    int dim[3] = {volume.dim[0], volume.dim[1], volume.dim[2]};
    UploadFloatTexture3D(&gpu.texture, dim, volume.density.data());
  }

  gpu.has_emission = !volume.emission.empty();
  if (gpu.has_emission) {
    int dim[3] = {volume.dim[0], volume.dim[1], volume.dim[2]};
    UploadFloatTexture3D(&gpu.emission_texture, dim, volume.emission.data());
    const float erange = volume.emission_max - volume.emission_min;
    gpu.emission_offset = volume.emission_min;
    gpu.emission_scale = erange > 1.0e-6f ? 1.0f / erange : 1.0f;
  }

  gpu.has_vector = !volume.vector3.empty();
  if (gpu.has_vector) {
    glGenTextures(1, &gpu.vector_texture);
    glBindTexture(GL_TEXTURE_3D, gpu.vector_texture);
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_R, GL_CLAMP_TO_EDGE);
    glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
    glTexImage3D(GL_TEXTURE_3D, 0, GL_RGB32F, volume.dim[0], volume.dim[1],
                 volume.dim[2], 0, GL_RGB, GL_FLOAT, volume.vector3.data());
    glBindTexture(GL_TEXTURE_3D, 0);
    gpu.vector_len_scale =
        volume.vector_max_len > 1.0e-6f ? 1.0f / volume.vector_max_len : 1.0f;
  }

  static const float kCubePositions[] = {
      0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0,
      0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1};
  static const uint32_t kCubeIndices[] = {
      0, 2, 1, 0, 3, 2,
      4, 5, 6, 4, 6, 7,
      0, 1, 5, 0, 5, 4,
      3, 6, 2, 3, 7, 6,
      0, 4, 7, 0, 7, 3,
      1, 2, 6, 1, 6, 5};

  glGenVertexArrays(1, &gpu.vao);
  glGenBuffers(1, &gpu.vbo);
  glGenBuffers(1, &gpu.ebo);
  glBindVertexArray(gpu.vao);
  glBindBuffer(GL_ARRAY_BUFFER, gpu.vbo);
  glBufferData(GL_ARRAY_BUFFER, sizeof(kCubePositions), kCubePositions, GL_STATIC_DRAW);
  glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, gpu.ebo);
  glBufferData(GL_ELEMENT_ARRAY_BUFFER, sizeof(kCubeIndices), kCubeIndices, GL_STATIC_DRAW);
  glVertexAttribPointer(0, 3, GL_FLOAT, GL_FALSE, 3 * sizeof(float), nullptr);
  glEnableVertexAttribArray(0);
  glBindVertexArray(0);
  gpu.index_count = static_cast<GLsizei>(sizeof(kCubeIndices) / sizeof(kCubeIndices[0]));

  gpu.internal_lines = BuildVolumeNodeLineMesh(volume, false);
  gpu.leaf_lines = BuildVolumeNodeLineMesh(volume, true);
  gpu.dense_bounds_lines = BuildDenseBoundsLineMesh(volume);
  return gpu;
}

void DestroyLineMesh(LineMesh* mesh) {
  if (!mesh) return;
  if (mesh->ebo) glDeleteBuffers(1, &mesh->ebo);
  if (mesh->vbo) glDeleteBuffers(1, &mesh->vbo);
  if (mesh->vao) glDeleteVertexArrays(1, &mesh->vao);
  *mesh = LineMesh{};
}

void DestroyVolume(GpuVolume* volume) {
  if (!volume) return;
  if (volume->texture) glDeleteTextures(1, &volume->texture);
  if (volume->emission_texture) glDeleteTextures(1, &volume->emission_texture);
  if (volume->vector_texture) glDeleteTextures(1, &volume->vector_texture);
  if (volume->ebo) glDeleteBuffers(1, &volume->ebo);
  if (volume->vbo) glDeleteBuffers(1, &volume->vbo);
  if (volume->vao) glDeleteVertexArrays(1, &volume->vao);
  DestroyLineMesh(&volume->internal_lines);
  DestroyLineMesh(&volume->leaf_lines);
  DestroyLineMesh(&volume->dense_bounds_lines);
  *volume = GpuVolume{};
}

void ClearGpuVolumes(AppState* app) {
  for (std::size_t i = 0; i < app->gpu_volumes.size(); ++i) {
    DestroyVolume(&app->gpu_volumes[i]);
  }
  app->gpu_volumes.clear();
}

bool ActiveVolumeHasDensity(const AppState& app) {
  return app.active_volume < app.gpu_volumes.size() &&
         app.gpu_volumes[app.active_volume].has_density;
}

void PrintVolumeList(const AppState& app) {
  for (std::size_t i = 0; i < app.scene.volumes.size(); ++i) {
    const VolumeData& volume = app.scene.volumes[i];
    std::cout << "  [" << i << "] " << volume.name;
    if (!volume.density.empty()) {
      std::cout << " dim=" << volume.dim[0] << "x" << volume.dim[1] << "x" << volume.dim[2]
                << " range=[" << volume.min_value << ", " << volume.max_value << "]";
    } else {
      std::cout << " topology";
    }
    if (i == app.active_volume) std::cout << " *";
    std::cout << "\n";
  }
}

bool SelectVolume(AppState* app, std::size_t index) {
  if (index >= app->gpu_volumes.size()) {
    std::cerr << "No VDB attribute/grid at index " << index << "\n";
    return false;
  }
  app->active_volume = index;
  if (index < app->scene.volumes.size() && !app->manual_window) {
    app->window_min = app->scene.volumes[index].min_value;
    app->window_max = app->scene.volumes[index].max_value;
  }
  if (!ActiveVolumeHasDensity(*app) && app->render_mode == VolumeRenderMode::Volume) {
    app->render_mode = VolumeRenderMode::GridOnly;
  }
  std::cout << "selected [" << index << "] " << app->scene.volumes[index].name << "\n";
  return true;
}

void ResetValueWindow(AppState* app) {
  if (app->active_volume >= app->scene.volumes.size()) return;
  const VolumeData& volume = app->scene.volumes[app->active_volume];
  app->window_min = volume.min_value;
  app->window_max = volume.max_value;
  app->manual_window = false;
}

void ClampValueWindow(AppState* app) {
  if (app->window_max < app->window_min + 1.0e-8f) {
    app->window_max = app->window_min + 1.0e-8f;
  }
}

bool SetPercentileValueWindow(AppState* app, float lower_percent, float upper_percent) {
  if (app->active_volume >= app->scene.volumes.size()) return false;
  const VolumeData& volume = app->scene.volumes[app->active_volume];
  if (volume.density.empty()) return false;
  std::vector<float> values = volume.density;
  std::sort(values.begin(), values.end());
  auto percentile = [&](float p) {
    p = std::max(0.0f, std::min(100.0f, p));
    const std::size_t idx = static_cast<std::size_t>(
        (p / 100.0f) * static_cast<float>(values.size() - 1));
    return values[idx];
  };
  app->window_min = percentile(lower_percent);
  app->window_max = percentile(upper_percent);
  ClampValueWindow(app);
  app->manual_window = true;
  return true;
}

void ClampClipBox(AppState* app);

bool SetClipToActiveBounds(AppState* app) {
  if (app->active_volume >= app->scene.volumes.size()) return false;
  const VolumeData& volume = app->scene.volumes[app->active_volume];
  if (!volume.has_active_bbox) return false;
  for (int axis = 0; axis < 3; ++axis) {
    app->clip_min[axis] = volume.active_uvw_min[axis];
    app->clip_max[axis] = volume.active_uvw_max[axis];
  }
  ClampClipBox(app);
  app->clip_enabled = true;
  return true;
}

Bounds ActiveVolumeBounds(const AppState& app) {
  if (app.active_volume < app.scene.volumes.size()) {
    return app.scene.volumes[app.active_volume].world_bounds;
  }
  return app.scene.bounds;
}

float Component(const Vec3& v, int axis) {
  if (axis == 0) return v.x;
  if (axis == 1) return v.y;
  return v.z;
}

bool RayIntersectBounds(const Vec3& ro, const Vec3& rd, const Bounds& bounds,
                        float* t_enter, float* t_exit) {
  if (!bounds.valid) return false;
  float enter = 0.0f;
  float exit = std::numeric_limits<float>::max();
  for (int axis = 0; axis < 3; ++axis) {
    const float origin = Component(ro, axis);
    const float dir = Component(rd, axis);
    const float mn = Component(bounds.min, axis);
    const float mx = Component(bounds.max, axis);
    if (std::fabs(dir) < 1.0e-8f) {
      if (origin < mn || origin > mx) return false;
      continue;
    }
    float t0 = (mn - origin) / dir;
    float t1 = (mx - origin) / dir;
    if (t0 > t1) std::swap(t0, t1);
    enter = std::max(enter, t0);
    exit = std::min(exit, t1);
    if (enter > exit) return false;
  }
  if (t_enter) *t_enter = enter;
  if (t_exit) *t_exit = exit;
  return exit >= 0.0f;
}

float SampleActiveVolumeNearest(AppState* app, const Vec3& uvw, int out_index[3]) {
  if (app->active_volume >= app->scene.volumes.size()) return 0.0f;
  const VolumeData& volume = app->scene.volumes[app->active_volume];
  if (volume.density.empty()) return 0.0f;
  const float u[3] = {
      std::max(0.0f, std::min(0.999999f, uvw.x)),
      std::max(0.0f, std::min(0.999999f, uvw.y)),
      std::max(0.0f, std::min(0.999999f, uvw.z)),
  };
  for (int axis = 0; axis < 3; ++axis) {
    out_index[axis] = std::max(
        0, std::min(volume.dim[axis] - 1, static_cast<int>(u[axis] * volume.dim[axis])));
  }
  const std::size_t idx =
      static_cast<std::size_t>(out_index[0]) +
      static_cast<std::size_t>(volume.dim[0]) *
          (static_cast<std::size_t>(out_index[1]) +
           static_cast<std::size_t>(volume.dim[1]) * static_cast<std::size_t>(out_index[2]));
  return idx < volume.density.size() ? volume.density[idx] : 0.0f;
}

Vec3 UvwFromWorld(const Bounds& bounds, const Vec3& p) {
  const Vec3 extent = bounds.max - bounds.min;
  Vec3 uvw{0.0f, 0.0f, 0.0f};
  uvw.x = extent.x != 0.0f ? (p.x - bounds.min.x) / extent.x : 0.0f;
  uvw.y = extent.y != 0.0f ? (p.y - bounds.min.y) / extent.y : 0.0f;
  uvw.z = extent.z != 0.0f ? (p.z - bounds.min.z) / extent.z : 0.0f;
  uvw.x = std::max(0.0f, std::min(1.0f, uvw.x));
  uvw.y = std::max(0.0f, std::min(1.0f, uvw.y));
  uvw.z = std::max(0.0f, std::min(1.0f, uvw.z));
  return uvw;
}

float ProbeVisibleScore(const AppState& app, float raw) {
  if (app.sdf_fog_mode) {
    if (app.active_volume >= app.gpu_volumes.size()) return -raw;
    return std::max(0.0f, -raw * app.gpu_volumes[app.active_volume].sdf_band_scale);
  }
  float mn = app.window_min;
  float mx = app.window_max;
  if (!app.manual_window && app.active_volume < app.scene.volumes.size()) {
    mn = app.scene.volumes[app.active_volume].min_value;
    mx = app.scene.volumes[app.active_volume].max_value;
  }
  const float scale = (mx - mn) > 1.0e-8f ? 1.0f / (mx - mn) : 1.0f;
  float norm = std::max(0.0f, std::min(1.0f, (raw - mn) * scale));
  if (app.invert_values) norm = 1.0f - norm;
  return std::pow(norm, std::max(app.value_gamma, 1.0e-4f));
}

bool ProbeAtCursor(AppState* app, double x, double y) {
  if (!ActiveVolumeHasDensity(*app)) return false;
  const Bounds bounds = ActiveVolumeBounds(*app);
  if (!bounds.valid || app->framebuffer_width <= 0 || app->framebuffer_height <= 0) {
    return false;
  }

  Vec3 right;
  Vec3 up;
  app->camera.localAxes(&right, &up);
  const Vec3 eye = app->camera.eye();
  const Vec3 forward = Normalize(app->camera.target - eye);
  const float aspect =
      static_cast<float>(app->framebuffer_width) / static_cast<float>(app->framebuffer_height);
  const float nx = static_cast<float>((2.0 * x) / app->framebuffer_width - 1.0);
  const float ny = static_cast<float>(1.0 - (2.0 * y) / app->framebuffer_height);
  const float tan_half = std::tan(kCameraFovYRadians * 0.5f);
  const Vec3 rd = Normalize(forward + right * (nx * aspect * tan_half) + up * (ny * tan_half));

  float t_enter = 0.0f;
  float t_exit = 0.0f;
  if (!RayIntersectBounds(eye, rd, bounds, &t_enter, &t_exit)) {
    app->has_probe = false;
    return false;
  }

  float t_probe = std::max(0.0f, (std::max(0.0f, t_enter) + t_exit) * 0.5f);
  int probe_index[3] = {0, 0, 0};
  if (app->probe_mode == 1) {
    const int steps = std::max(1, std::min(512, app->sample_steps));
    float best_score = -std::numeric_limits<float>::infinity();
    for (int i = 0; i < steps; ++i) {
      const float s = (static_cast<float>(i) + 0.5f) / static_cast<float>(steps);
      const float t = std::max(0.0f, t_enter) + (t_exit - std::max(0.0f, t_enter)) * s;
      const Vec3 uvw = UvwFromWorld(bounds, eye + rd * t);
      int idx[3] = {0, 0, 0};
      const float raw = SampleActiveVolumeNearest(app, uvw, idx);
      const float score = ProbeVisibleScore(*app, raw);
      if (score > best_score) {
        best_score = score;
        t_probe = t;
        probe_index[0] = idx[0];
        probe_index[1] = idx[1];
        probe_index[2] = idx[2];
      }
    }
  }
  const Vec3 p = eye + rd * t_probe;
  const Vec3 uvw = UvwFromWorld(bounds, p);

  app->probe_world = p;
  app->probe_uvw = uvw;
  app->probe_value = SampleActiveVolumeNearest(app, uvw, app->probe_index);
  if (app->probe_mode == 1) {
    app->probe_index[0] = probe_index[0];
    app->probe_index[1] = probe_index[1];
    app->probe_index[2] = probe_index[2];
  }
  app->has_probe = true;
  std::cout << "probe [" << app->probe_index[0] << ", " << app->probe_index[1] << ", "
            << app->probe_index[2] << "] value=" << app->probe_value << "\n";
  return true;
}

void FrameSelectedVolume(AppState* app) {
  const Bounds bounds = ActiveVolumeBounds(*app);
  if (bounds.valid) app->camera.resetToBounds(bounds);
}

void SetCameraPreset(AppState* app, int preset) {
  const Bounds bounds = ActiveVolumeBounds(*app);
  app->camera.resetToBounds(bounds);
  if (preset == 0) {
    app->camera.longitude = 0.0f;
    app->camera.latitude = 0.0f;
  } else if (preset == 1) {
    app->camera.longitude = 0.0f;
    app->camera.latitude = 89.0f;
  } else {
    app->camera.longitude = 90.0f;
    app->camera.latitude = 0.0f;
  }
}

void ClampClipBox(AppState* app) {
  for (int a = 0; a < 3; ++a) {
    app->clip_min[a] = std::max(0.0f, std::min(0.98f, app->clip_min[a]));
    app->clip_max[a] = std::max(0.02f, std::min(1.0f, app->clip_max[a]));
    if (app->clip_min[a] > app->clip_max[a] - 0.02f) {
      const float center = (app->clip_min[a] + app->clip_max[a]) * 0.5f;
      app->clip_min[a] = std::max(0.0f, center - 0.01f);
      app->clip_max[a] = std::min(1.0f, center + 0.01f);
    }
  }
}

void AdjustClipBox(AppState* app, float delta) {
  for (int a = 0; a < 3; ++a) {
    app->clip_min[a] += delta;
    app->clip_max[a] -= delta;
  }
  ClampClipBox(app);
  app->clip_enabled = true;
  std::cout << "clip box: [" << app->clip_min[0] << ", " << app->clip_min[1] << ", "
            << app->clip_min[2] << "] - [" << app->clip_max[0] << ", "
            << app->clip_max[1] << ", " << app->clip_max[2] << "]\n";
}

void SaveScreenshot(AppState* app, const std::string& requested_path = std::string()) {
  const int w = app->framebuffer_width;
  const int h = app->framebuffer_height;
  if (w <= 0 || h <= 0) return;
  std::vector<uint8_t> rgba(static_cast<std::size_t>(w) * static_cast<std::size_t>(h) * 4);
  std::vector<uint8_t> flipped(rgba.size());
  glPixelStorei(GL_PACK_ALIGNMENT, 1);
  glReadPixels(0, 0, w, h, GL_RGBA, GL_UNSIGNED_BYTE, rgba.data());
  const std::size_t row_bytes = static_cast<std::size_t>(w) * 4;
  for (int y = 0; y < h; ++y) {
    std::memcpy(flipped.data() + static_cast<std::size_t>(y) * row_bytes,
                rgba.data() + static_cast<std::size_t>(h - 1 - y) * row_bytes,
                row_bytes);
  }
  char fallback[64];
  std::snprintf(fallback, sizeof(fallback), "tvdbview_%04d.png", app->screenshot_counter++);
  const std::string filename = requested_path.empty() ? std::string(fallback) : requested_path;
  if (stbi_write_png(filename.c_str(), w, h, 4, flipped.data(), w * 4)) {
    std::cout << "saved screenshot: " << filename << "\n";
  } else {
    std::cerr << "failed to save screenshot: " << filename << "\n";
  }
}

bool SavePathTraceImage(AppState* app, const std::string& requested_path = std::string()) {
  const int w = app->path_trace_width;
  const int h = app->path_trace_height;
  if (w <= 0 || h <= 0 || app->path_trace_rgba.empty()) {
    std::cerr << "No path trace image to save.\n";
    return false;
  }
  char fallback[64];
  std::snprintf(fallback, sizeof(fallback), "tvdbview_pt_%04d.png", app->screenshot_counter++);
  const std::string filename = requested_path.empty() ? std::string(fallback) : requested_path;
  if (stbi_write_png(filename.c_str(), w, h, 4, app->path_trace_rgba.data(), w * 4)) {
    std::cout << "saved path trace image: " << filename << "\n";
    return true;
  }
  std::cerr << "failed to save path trace image: " << filename << "\n";
  return false;
}

void ResetPathTrace(AppState* app);

bool LoadSceneIntoApp(AppState* app, const std::string& path) {
  SceneData scene;
  std::string error;
  if (!LoadVdbScene(path, &scene, &error)) {
    std::cerr << "Failed to load " << path << ": " << error << "\n";
    return false;
  }

  ClearGpuVolumes(app);
  app->scene = std::move(scene);
  app->gpu_volumes.reserve(app->scene.volumes.size());
  for (std::size_t i = 0; i < app->scene.volumes.size(); ++i) {
    app->gpu_volumes.push_back(UploadVolume(app->scene.volumes[i]));
  }
  app->active_volume = 0;
  app->camera.resetToBounds(app->scene.bounds);
  app->current_path = path;
  if (!app->scene.volumes.empty()) {
    bool has_density = false;
    for (std::size_t i = 0; i < app->gpu_volumes.size(); ++i) {
      has_density = has_density || app->gpu_volumes[i].has_density;
    }
    app->render_mode = has_density ? VolumeRenderMode::VolumeWithGrid
                                   : VolumeRenderMode::GridOnly;
    for (std::size_t i = 0; i < app->gpu_volumes.size(); ++i) {
      if (app->gpu_volumes[i].has_density) {
        app->active_volume = i;
        break;
      }
    }
  }
  ResetValueWindow(app);
  app->path_trace_fingerprint.clear();
  ResetPathTrace(app);

  std::cout << "Loaded " << path << "\n";
  for (std::size_t i = 0; i < app->scene.notes.size(); ++i) {
    std::cout << "  " << app->scene.notes[i] << "\n";
  }
  std::cout << "Attributes/grids:\n";
  PrintVolumeList(*app);
  return true;
}

bool ApplyCliOptionsAfterLoad(AppState* app, const CliOptions& opts) {
  if (opts.has_grid) {
    int grid_index = -1;
    bool selected = false;
    if (ParseIntArg(opts.grid_selector, &grid_index) && grid_index >= 0) {
      selected = SelectVolume(app, static_cast<std::size_t>(grid_index));
    } else {
      for (std::size_t i = 0; i < app->scene.volumes.size(); ++i) {
        if (app->scene.volumes[i].name == opts.grid_selector) {
          selected = SelectVolume(app, i);
          break;
        }
      }
      if (!selected) {
        std::cerr << "No grid named '" << opts.grid_selector << "'\n";
      }
    }
    if (!selected) return false;
  }
  if (opts.has_color) app->color_mode = opts.color_mode;
  if (opts.has_render_mode) app->render_mode = opts.render_mode;
  if (opts.has_gain) app->density_gain = std::max(0.001f, opts.density_gain);
  if (opts.has_window) {
    app->window_min = opts.window_min;
    app->window_max = opts.window_max;
    ClampValueWindow(app);
    app->manual_window = true;
  }
  if (opts.has_percentile_window) {
    SetPercentileValueWindow(app, opts.window_percentile_min, opts.window_percentile_max);
  }
  if (opts.has_gamma) app->value_gamma = std::max(0.001f, opts.value_gamma);
  if (opts.has_opacity_power) app->opacity_power = std::max(0.001f, opts.opacity_power);
  if (opts.invert_values) app->invert_values = true;
  if (opts.has_steps) app->sample_steps = std::max(1, std::min(512, opts.sample_steps));
  if (opts.has_ray_mode) app->ray_mode = opts.ray_mode;
  if (opts.has_iso_threshold) {
    app->iso_threshold = std::max(0.0f, std::min(1.0f, opts.iso_threshold));
  }
  if (opts.has_path_trace_scale) {
    app->path_trace_scale = std::max(1, std::min(16, opts.path_trace_scale));
  }
  if (opts.has_path_trace_rows) {
    app->path_trace_rows_per_frame = std::max(1, std::min(4096, opts.path_trace_rows_per_frame));
  }
  if (opts.has_path_trace_depth) {
    app->path_trace_max_depth = std::max(1, std::min(8, opts.path_trace_max_depth));
  }
  if (opts.has_path_trace_backend) app->path_trace_backend = opts.path_trace_backend;
  if (opts.has_path_trace_capture_samples) {
    app->path_trace_capture_samples =
        std::max(0, std::min(1000000, opts.path_trace_capture_samples));
  }
  if (opts.has_sun) {
    app->path_trace_sun_angle = std::max(-5.0f, std::min(89.0f, opts.path_trace_sun_angle));
    app->path_trace_sun_azimuth = opts.path_trace_sun_azimuth;
  }
  if (opts.has_sun_strength) {
    app->path_trace_sun_strength = std::max(0.0f, opts.path_trace_sun_strength);
  }
  if (opts.has_sky_strength) {
    app->path_trace_sky_strength = std::max(0.0f, opts.path_trace_sky_strength);
  }
  if (opts.has_path_trace_albedo) {
    app->path_trace_albedo = std::max(0.0f, std::min(1.0f, opts.path_trace_albedo));
  }
  if (opts.has_shade_enabled) app->shade_enabled = opts.shade_enabled;
  if (opts.has_shade_strength) {
    app->shade_strength = std::max(0.0f, std::min(1.0f, opts.shade_strength));
  }
  if (opts.has_light_dir) app->light_dir = Normalize(opts.light_dir);
  if (opts.has_slice) {
    app->slice_axis = opts.slice_axis;
    app->slice_pos = opts.slice_pos;
    app->slice_thickness = opts.slice_thickness;
  }
  if (opts.has_clip) {
    app->clip_enabled = true;
    for (int i = 0; i < 3; ++i) {
      app->clip_min[i] = opts.clip_min[i];
      app->clip_max[i] = opts.clip_max[i];
    }
    ClampClipBox(app);
  }
  if (opts.clip_active) SetClipToActiveBounds(app);
  if (opts.no_grid && ActiveVolumeHasDensity(*app)) {
    app->render_mode = VolumeRenderMode::Volume;
  }
  if (opts.sdf_fog_mode) app->sdf_fog_mode = true;
  if (opts.hide_internal_boxes) app->show_internal_boxes = false;
  if (opts.hide_leaf_boxes) app->show_leaf_boxes = false;
  if (opts.hide_dense_bounds) app->show_dense_bounds = false;
  if (opts.hide_hud) app->show_hud = false;
  if (opts.hide_panel) app->show_control_panel = false;
  if (opts.has_camera) {
    app->camera.longitude = opts.camera_longitude;
    app->camera.latitude = opts.camera_latitude;
    app->camera.distance = opts.camera_distance;
    app->camera.target = opts.camera_target;
  }
  if (opts.has_capture) {
    app->capture_path = opts.capture_path;
    app->pending_capture = true;
    app->quit_after_capture = opts.quit_after_capture;
  }
  return true;
}

#if defined(TVDBVIEW_ENABLE_NFD)
void OpenVdbDialog(AppState* app) {
  if (!app->nfd_initialized) {
    if (NFD_Init() != NFD_OKAY) {
      std::cerr << "Native file dialog init failed: " << NFD_GetError() << "\n";
      return;
    }
    app->nfd_initialized = true;
  }
  const nfdu8filteritem_t filters[] = {{"VDB files", "vdb"}, {"All files", "*"}};
  nfdopendialogu8args_t args = {};
  args.filterList = filters;
  args.filterCount = static_cast<nfdfiltersize_t>(sizeof(filters) / sizeof(filters[0]));
  nfdu8char_t* selected_path = nullptr;
  const nfdresult_t result = NFD_OpenDialogU8_With(&selected_path, &args);
  if (result == NFD_OKAY) {
    const std::string path(selected_path);
    NFD_FreePathU8(selected_path);
    LoadSceneIntoApp(app, path);
  } else if (result == NFD_ERROR) {
    std::cerr << "Native file dialog failed: " << NFD_GetError() << "\n";
  }
}
#else
void OpenVdbDialog(AppState*) {
  std::cerr << "This build does not include native file dialog support.\n";
}
#endif

void UpdateWindowTitle(AppState* app) {
  std::string title = "tvdbview";
  if (!app->current_path.empty()) title += " - " + app->current_path;
  if (app->active_volume < app->scene.volumes.size()) {
    title += " <" + std::to_string(app->active_volume) + ":" +
             app->scene.volumes[app->active_volume].name + ">";
  }
  title += " [" + std::string(RenderModeLabel(app->render_mode)) +
           ", " + ColorModeLabel(app->color_mode) + "]";
  glfwSetWindowTitle(app->window, title.c_str());
}

std::string FormatFloat(float v) {
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%.9g", v);
  return std::string(buf);
}

std::string ShellQuote(const std::string& text) {
  if (text.empty()) return "''";
  bool plain = true;
  for (char c : text) {
    const bool ok = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                    (c >= '0' && c <= '9') || c == '/' || c == '_' ||
                    c == '-' || c == '.' || c == ':' || c == '+';
    if (!ok) {
      plain = false;
      break;
    }
  }
  if (plain) return text;
  std::string quoted = "'";
  for (char c : text) {
    if (c == '\'') {
      quoted += "'\\''";
    } else {
      quoted += c;
    }
  }
  quoted += "'";
  return quoted;
}

std::string BuildCurrentCommandLine(const AppState& app) {
  std::ostringstream ss;
  ss << "./build-tvdbview/tvdbview";
  if (!app.current_path.empty()) ss << " " << ShellQuote(app.current_path);
  ss << " --size " << app.window_width << "x" << app.window_height;
  if (app.active_volume < app.scene.volumes.size()) ss << " --grid " << app.active_volume;
  ss << " --display " << RenderModeLabel(app.render_mode);
  ss << " --color " << ColorModeLabel(app.color_mode);
  ss << " --gain " << FormatFloat(app.density_gain);
  if (app.manual_window) {
    ss << " --window " << FormatFloat(app.window_min) << ":" << FormatFloat(app.window_max);
  }
  if (std::fabs(app.value_gamma - 1.0f) > 1.0e-6f) {
    ss << " --gamma " << FormatFloat(app.value_gamma);
  }
  if (std::fabs(app.opacity_power - 1.0f) > 1.0e-6f) {
    ss << " --opacity-power " << FormatFloat(app.opacity_power);
  }
  if (app.invert_values) ss << " --invert";
  ss << " --steps " << app.sample_steps;
  ss << " --ray " << RayModeLabel(app.ray_mode);
  if (app.ray_mode == VolumeRayMode::Iso ||
      std::fabs(app.iso_threshold - 0.5f) > 1.0e-6f) {
    ss << " --iso " << FormatFloat(app.iso_threshold);
  }
  if (app.ray_mode == VolumeRayMode::PathTraceCpu) {
    ss << " --pt-scale " << app.path_trace_scale;
    if (app.path_trace_backend == 1) ss << " --pt-backend gpu";
    if (app.path_trace_backend == 2) ss << " --pt-backend cpu";
    if (app.path_trace_backend == 3) ss << " --pt-backend vulkan";
    if (app.path_trace_capture_samples > 0) {
      ss << " --pt-spp " << app.path_trace_capture_samples;
    }
    ss << " --pt-rows " << app.path_trace_rows_per_frame;
    ss << " --pt-depth " << app.path_trace_max_depth;
    ss << " --sun " << FormatFloat(app.path_trace_sun_angle) << ":"
       << FormatFloat(app.path_trace_sun_azimuth);
    ss << " --sun-strength " << FormatFloat(app.path_trace_sun_strength);
    ss << " --sky-strength " << FormatFloat(app.path_trace_sky_strength);
    ss << " --pt-albedo " << FormatFloat(app.path_trace_albedo);
  }
  ss << (app.shade_enabled ? " --shade" : " --no-shade");
  if (std::fabs(app.shade_strength - 0.65f) > 1.0e-6f) {
    ss << " --shade-strength " << FormatFloat(app.shade_strength);
  }
  ss << " --light " << FormatFloat(app.light_dir.x) << "," << FormatFloat(app.light_dir.y)
     << "," << FormatFloat(app.light_dir.z);
  if (app.sdf_fog_mode) ss << " --sdf-fog";
  if (app.slice_axis > 0) {
    ss << " --slice " << SliceAxisLabel(app.slice_axis) << ":" << FormatFloat(app.slice_pos)
       << ":" << FormatFloat(app.slice_thickness);
  }
  if (app.clip_enabled) {
    ss << " --clip " << FormatFloat(app.clip_min[0]) << ","
       << FormatFloat(app.clip_min[1]) << "," << FormatFloat(app.clip_min[2]) << ":"
       << FormatFloat(app.clip_max[0]) << "," << FormatFloat(app.clip_max[1]) << ","
       << FormatFloat(app.clip_max[2]);
  }
  if (!app.show_internal_boxes) ss << " --no-internal-boxes";
  if (!app.show_leaf_boxes) ss << " --no-leaf-boxes";
  if (!app.show_dense_bounds) ss << " --no-dense-bounds";
  if (!app.show_hud) ss << " --hide-hud";
  if (!app.show_control_panel) ss << " --hide-panel";
  ss << " --camera " << FormatFloat(app.camera.longitude) << ","
     << FormatFloat(app.camera.latitude) << "," << FormatFloat(app.camera.distance) << ":"
     << FormatFloat(app.camera.target.x) << "," << FormatFloat(app.camera.target.y) << ","
     << FormatFloat(app.camera.target.z);
  if (!app.capture_path.empty()) ss << " --capture " << ShellQuote(app.capture_path);
  if (app.quit_after_capture) ss << " --quit";
  return ss.str();
}

float Saturate(float v) {
  return std::max(0.0f, std::min(1.0f, v));
}

Vec3 Mix(const Vec3& a, const Vec3& b, float t) {
  return a * (1.0f - t) + b * t;
}

Vec3 Mul(const Vec3& a, const Vec3& b) {
  return Vec3{a.x * b.x, a.y * b.y, a.z * b.z};
}

Vec3 ClampColor(const Vec3& c) {
  return Vec3{std::max(0.0f, c.x), std::max(0.0f, c.y), std::max(0.0f, c.z)};
}

uint32_t HashU32(uint32_t x) {
  x ^= x >> 16;
  x *= 0x7feb352du;
  x ^= x >> 15;
  x *= 0x846ca68bu;
  x ^= x >> 16;
  return x;
}

float RandomFloat(uint32_t* state) {
  *state = HashU32(*state + 0x9e3779b9u);
  return static_cast<float>(*state & 0x00ffffffu) / static_cast<float>(0x01000000u);
}

Vec3 RandomUnitVector(uint32_t* state) {
  const float z = 1.0f - 2.0f * RandomFloat(state);
  const float a = 2.0f * kPi * RandomFloat(state);
  const float r = std::sqrt(std::max(0.0f, 1.0f - z * z));
  return Vec3{r * std::cos(a), z, r * std::sin(a)};
}

Vec3 SunDirection(const AppState& app) {
  const float elev = app.path_trace_sun_angle * kPi / 180.0f;
  const float az = app.path_trace_sun_azimuth * kPi / 180.0f;
  const float ce = std::cos(elev);
  return Normalize(Vec3{ce * std::sin(az), std::sin(elev), ce * std::cos(az)});
}

Vec3 SunSkyEnvironment(const AppState& app, const Vec3& dir) {
  const Vec3 sun_dir = SunDirection(app);
  const float up = Saturate(dir.y * 0.5f + 0.5f);
  const Vec3 horizon{0.78f, 0.86f, 1.0f};
  const Vec3 zenith{0.10f, 0.32f, 0.85f};
  Vec3 sky = Mix(horizon, zenith, up) * app.path_trace_sky_strength;
  const float sun_dot = std::max(0.0f, Dot(Normalize(dir), sun_dir));
  const float disk = std::pow(sun_dot, 900.0f);
  const Vec3 sun_color{1.0f, 0.86f, 0.62f};
  return sky + sun_color * (disk * app.path_trace_sun_strength);
}

float NormalizedVolumeValue(const AppState& app, float raw) {
  if (app.sdf_fog_mode) {
    if (app.active_volume >= app.gpu_volumes.size()) return 0.0f;
    return Saturate(-raw * app.gpu_volumes[app.active_volume].sdf_band_scale);
  }
  float mn = app.window_min;
  float mx = app.window_max;
  if (!app.manual_window && app.active_volume < app.scene.volumes.size()) {
    mn = app.scene.volumes[app.active_volume].min_value;
    mx = app.scene.volumes[app.active_volume].max_value;
  }
  const float scale = (mx - mn) > 1.0e-8f ? 1.0f / (mx - mn) : 1.0f;
  float norm = Saturate((raw - mn) * scale);
  if (app.invert_values) norm = 1.0f - norm;
  return std::pow(norm, std::max(app.value_gamma, 1.0e-4f));
}

Vec3 CpuJetColor(float t) {
  t = Saturate(t);
  return Vec3{
      Saturate(1.5f - std::fabs(4.0f * t - 3.0f)),
      Saturate(1.5f - std::fabs(4.0f * t - 2.0f)),
      Saturate(1.5f - std::fabs(4.0f * t - 1.0f)),
  };
}

Vec3 CpuBlackbody(float t) {
  t = Saturate(t);
  const Vec3 dark{0.0f, 0.0f, 0.0f};
  const Vec3 red{1.0f, 0.12f, 0.02f};
  const Vec3 orange{1.0f, 0.55f, 0.05f};
  const Vec3 yellow{1.0f, 0.92f, 0.35f};
  const Vec3 white{1.0f, 1.0f, 0.95f};
  if (t < 0.25f) return Mix(dark, red, t / 0.25f);
  if (t < 0.5f) return Mix(red, orange, (t - 0.25f) / 0.25f);
  if (t < 0.75f) return Mix(orange, yellow, (t - 0.5f) / 0.25f);
  return Mix(yellow, white, (t - 0.75f) / 0.25f);
}

Vec3 CpuValueColor(const AppState& app, float norm) {
  if (app.color_mode == VolumeColorMode::Jet) return CpuJetColor(norm);
  if (app.color_mode == VolumeColorMode::Blackbody) return CpuBlackbody(norm);
  return Vec3{norm, norm, norm};
}

bool UvwInsideClipAndSlice(const AppState& app, const Vec3& uvw) {
  if (app.clip_enabled) {
    if (uvw.x < app.clip_min[0] || uvw.y < app.clip_min[1] || uvw.z < app.clip_min[2] ||
        uvw.x > app.clip_max[0] || uvw.y > app.clip_max[1] || uvw.z > app.clip_max[2]) {
      return false;
    }
  }
  if (app.slice_axis > 0) {
    const float s = app.slice_axis == 1 ? uvw.x : (app.slice_axis == 2 ? uvw.y : uvw.z);
    if (std::fabs(s - app.slice_pos) > app.slice_thickness * 0.5f) return false;
  }
  return true;
}

float SampleVolumeNormNearest(const AppState& app, const VolumeData& volume, const Vec3& uvw) {
  if (volume.density.empty() || !UvwInsideClipAndSlice(app, uvw)) return 0.0f;
  int idx[3] = {};
  const float raw = SampleActiveVolumeNearest(const_cast<AppState*>(&app), uvw, idx);
  return NormalizedVolumeValue(app, raw);
}

float ShadowTransmittance(const AppState& app, const VolumeData& volume, const Bounds& bounds,
                          const Vec3& p, const Vec3& light_dir) {
  float t_enter = 0.0f;
  float t_exit = 0.0f;
  if (!RayIntersectBounds(p + light_dir * 1.0e-4f, light_dir, bounds, &t_enter, &t_exit)) {
    return 1.0f;
  }
  const Vec3 ex = bounds.max - bounds.min;
  const float max_extent = std::max(ex.x, std::max(ex.y, ex.z));
  const int steps = 32;
  const float t0 = std::max(0.0f, t_enter);
  const float dt = (t_exit - t0) / static_cast<float>(steps);
  float tr = 1.0f;
  for (int i = 0; i < steps; ++i) {
    const float t = t0 + (static_cast<float>(i) + 0.5f) * dt;
    const Vec3 uvw = UvwFromWorld(bounds, p + light_dir * t);
    const float norm = SampleVolumeNormNearest(app, volume, uvw);
    const float sigma_t = std::pow(norm, std::max(app.opacity_power, 1.0e-4f)) *
                          app.density_gain / std::max(max_extent, 1.0e-4f);
    tr *= std::exp(-sigma_t * dt);
    if (tr < 0.01f) break;
  }
  return tr;
}

Vec3 TraceVolumePathCpu(const AppState& app, const VolumeData& volume, const Bounds& bounds,
                        const Vec3& ray_origin, const Vec3& ray_dir, uint32_t* rng) {
  Vec3 origin = ray_origin;
  Vec3 dir = ray_dir;
  Vec3 throughput{1.0f, 1.0f, 1.0f};
  Vec3 radiance{0.0f, 0.0f, 0.0f};
  const Vec3 ex = bounds.max - bounds.min;
  const float max_extent = std::max(ex.x, std::max(ex.y, ex.z));
  const Vec3 sun_dir = SunDirection(app);
  const Vec3 sun_color{1.0f, 0.86f, 0.62f};

  for (int depth = 0; depth < app.path_trace_max_depth; ++depth) {
    float t_enter = 0.0f;
    float t_exit = 0.0f;
    if (!RayIntersectBounds(origin, dir, bounds, &t_enter, &t_exit)) {
      radiance = radiance + Mul(throughput, SunSkyEnvironment(app, dir));
      break;
    }
    const float t0 = std::max(0.0f, t_enter);
    const int steps = std::max(8, std::min(256, app.sample_steps));
    const float dt = (t_exit - t0) / static_cast<float>(steps);
    float transmittance = 1.0f;
    bool scattered = false;
    for (int i = 0; i < steps; ++i) {
      const float jitter = RandomFloat(rng);
      const float t = t0 + (static_cast<float>(i) + jitter) * dt;
      const Vec3 p = origin + dir * t;
      const Vec3 uvw = UvwFromWorld(bounds, p);
      const float norm = SampleVolumeNormNearest(app, volume, uvw);
      const float sigma_t = std::pow(norm, std::max(app.opacity_power, 1.0e-4f)) *
                            app.density_gain / std::max(max_extent, 1.0e-4f);
      const float step_tr = std::exp(-sigma_t * dt);
      if (sigma_t > 1.0e-6f && RandomFloat(rng) > step_tr) {
        const Vec3 medium_color = CpuValueColor(app, norm);
        const float sun_vis = ShadowTransmittance(app, volume, bounds, p, sun_dir);
        const Vec3 direct = sun_color * (app.path_trace_sun_strength * sun_vis * 0.08f) +
                            SunSkyEnvironment(app, Vec3{0.0f, 1.0f, 0.0f}) * 0.12f;
        throughput = Mul(throughput * transmittance, medium_color) * app.path_trace_albedo;
        radiance = radiance + Mul(throughput, direct);
        origin = p + dir * 1.0e-4f;
        dir = RandomUnitVector(rng);
        scattered = true;
        break;
      }
      transmittance *= step_tr;
      if (transmittance < 0.003f) break;
    }
    if (!scattered) {
      radiance = radiance + Mul(throughput * transmittance, SunSkyEnvironment(app, dir));
      break;
    }
  }
  return ClampColor(radiance);
}

std::string PathTraceFingerprint(const AppState& app) {
  std::ostringstream ss;
  ss << app.framebuffer_width << "x" << app.framebuffer_height << ":"
     << app.active_volume << ":" << app.path_trace_scale << ":"
     << app.camera.longitude << "," << app.camera.latitude << "," << app.camera.distance
     << "," << app.camera.target.x << "," << app.camera.target.y << "," << app.camera.target.z
     << ":" << BuildCurrentCommandLine(app);
  return ss.str();
}

void ResetPathTrace(AppState* app) {
  app->path_trace_next_row = 0;
  app->path_trace_completed_passes = 0;
  app->path_trace_last_backend = "none";
  std::fill(app->path_trace_accum.begin(), app->path_trace_accum.end(), Vec3{0.0f, 0.0f, 0.0f});
  std::fill(app->path_trace_sample_counts.begin(), app->path_trace_sample_counts.end(), 0u);
  if (app->path_trace_accum_texture && app->path_trace_width > 0 && app->path_trace_height > 0) {
    std::vector<float> zeros(static_cast<std::size_t>(app->path_trace_width) *
                             static_cast<std::size_t>(app->path_trace_height) * 4, 0.0f);
    glBindTexture(GL_TEXTURE_2D, app->path_trace_accum_texture);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA32F, app->path_trace_width,
                 app->path_trace_height, 0, GL_RGBA, GL_FLOAT, zeros.data());
  }
}

void EnsurePathTraceBuffers(AppState* app) {
  const int scale = std::max(1, app->path_trace_scale);
  const int w = std::max(1, app->framebuffer_width / scale);
  const int h = std::max(1, app->framebuffer_height / scale);
  const std::string fingerprint = PathTraceFingerprint(*app);
  if (w != app->path_trace_width || h != app->path_trace_height) {
    app->path_trace_width = w;
    app->path_trace_height = h;
    app->path_trace_accum.assign(static_cast<std::size_t>(w) * h, Vec3{0.0f, 0.0f, 0.0f});
    app->path_trace_sample_counts.assign(static_cast<std::size_t>(w) * h, 0u);
    app->path_trace_rgba.assign(static_cast<std::size_t>(w) * h * 4, 0u);
    if (!app->path_trace_texture) glGenTextures(1, &app->path_trace_texture);
    if (!app->path_trace_accum_texture) glGenTextures(1, &app->path_trace_accum_texture);
    glBindTexture(GL_TEXTURE_2D, app->path_trace_texture);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA8, w, h, 0, GL_RGBA, GL_UNSIGNED_BYTE,
                 app->path_trace_rgba.data());
    glBindTexture(GL_TEXTURE_2D, app->path_trace_accum_texture);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA32F, w, h, 0, GL_RGBA, GL_FLOAT, nullptr);
    app->path_trace_fingerprint.clear();
  }
  if (fingerprint != app->path_trace_fingerprint) {
    app->path_trace_fingerprint = fingerprint;
    ResetPathTrace(app);
  }
}

void UpdatePathTraceCpu(AppState* app) {
  if (app->active_volume >= app->scene.volumes.size()) return;
  const VolumeData& volume = app->scene.volumes[app->active_volume];
  const Bounds bounds = ActiveVolumeBounds(*app);
  if (volume.density.empty() || !bounds.valid) return;
  EnsurePathTraceBuffers(app);
  const int w = app->path_trace_width;
  const int h = app->path_trace_height;
  if (w <= 0 || h <= 0) return;

  Vec3 right;
  Vec3 up;
  app->camera.localAxes(&right, &up);
  const Vec3 eye = app->camera.eye();
  const Vec3 forward = Normalize(app->camera.target - eye);
  const float aspect = static_cast<float>(w) / static_cast<float>(h);
  const float tan_half = std::tan(kCameraFovYRadians * 0.5f);
  const int rows = std::max(1, app->path_trace_rows_per_frame);
  for (int rr = 0; rr < rows; ++rr) {
    const int y = app->path_trace_next_row;
    for (int x = 0; x < w; ++x) {
      const std::size_t idx = static_cast<std::size_t>(x) + static_cast<std::size_t>(w) * y;
      uint32_t rng = HashU32(static_cast<uint32_t>(x + 1) * 1973u ^
                             static_cast<uint32_t>(y + 1) * 9277u ^
                             static_cast<uint32_t>(app->path_trace_sample_counts[idx] + 1) *
                                 26699u);
      const float jx = RandomFloat(&rng);
      const float jy = RandomFloat(&rng);
      const float nx = ((static_cast<float>(x) + jx) / static_cast<float>(w)) * 2.0f - 1.0f;
      const float ny = 1.0f - ((static_cast<float>(y) + jy) / static_cast<float>(h)) * 2.0f;
      const Vec3 rd = Normalize(forward + right * (nx * aspect * tan_half) +
                                up * (ny * tan_half));
      const Vec3 c = TraceVolumePathCpu(*app, volume, bounds, eye, rd, &rng);
      app->path_trace_accum[idx] = app->path_trace_accum[idx] + c;
      app->path_trace_sample_counts[idx] += 1;
      const float inv_n = 1.0f / static_cast<float>(app->path_trace_sample_counts[idx]);
      Vec3 avg = app->path_trace_accum[idx] * inv_n;
      avg = Vec3{std::pow(std::max(0.0f, avg.x), 1.0f / 2.2f),
                 std::pow(std::max(0.0f, avg.y), 1.0f / 2.2f),
                 std::pow(std::max(0.0f, avg.z), 1.0f / 2.2f)};
      app->path_trace_rgba[idx * 4 + 0] = static_cast<uint8_t>(Saturate(avg.x) * 255.0f);
      app->path_trace_rgba[idx * 4 + 1] = static_cast<uint8_t>(Saturate(avg.y) * 255.0f);
      app->path_trace_rgba[idx * 4 + 2] = static_cast<uint8_t>(Saturate(avg.z) * 255.0f);
      app->path_trace_rgba[idx * 4 + 3] = 255;
    }
    app->path_trace_next_row = (app->path_trace_next_row + 1) % h;
    if (app->path_trace_next_row == 0) ++app->path_trace_completed_passes;
  }
  glBindTexture(GL_TEXTURE_2D, app->path_trace_texture);
  glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
  glTexSubImage2D(GL_TEXTURE_2D, 0, 0, 0, w, h, GL_RGBA, GL_UNSIGNED_BYTE,
                  app->path_trace_rgba.data());
  app->path_trace_last_backend = "cpu";
}

bool UpdatePathTraceCompute(AppState* app) {
  if (!app->path_trace_compute_available || !app->path_trace_compute_program) return false;
  if (app->active_volume >= app->gpu_volumes.size() ||
      app->active_volume >= app->scene.volumes.size()) {
    return false;
  }
  const GpuVolume& gpu_volume = app->gpu_volumes[app->active_volume];
  if (!gpu_volume.has_density || !gpu_volume.texture || !gpu_volume.world_bounds.valid) {
    return false;
  }
  EnsurePathTraceBuffers(app);
  const int w = app->path_trace_width;
  const int h = app->path_trace_height;
  if (w <= 0 || h <= 0) return false;

  Vec3 right;
  Vec3 up;
  app->camera.localAxes(&right, &up);
  const Vec3 eye = app->camera.eye();
  const Vec3 forward = Normalize(app->camera.target - eye);
  const Vec3 ex = gpu_volume.world_bounds.max - gpu_volume.world_bounds.min;
  const float max_extent = std::max(ex.x, std::max(ex.y, ex.z));
  float value_offset = gpu_volume.value_offset;
  float value_scale = gpu_volume.value_scale;
  if (app->manual_window) {
    ClampValueWindow(app);
    const float value_range = app->window_max - app->window_min;
    value_offset = app->window_min;
    value_scale = value_range > 1.0e-8f ? 1.0f / value_range : 1.0f;
  }

  glUseProgram(app->path_trace_compute_program);
  glActiveTexture(GL_TEXTURE0);
  glBindTexture(GL_TEXTURE_3D, gpu_volume.texture);
  glUniform1i(glGetUniformLocation(app->path_trace_compute_program, "uVolume"), 0);
  glBindImageTexture(0, app->path_trace_accum_texture, 0, GL_FALSE, 0, GL_READ_WRITE,
                     GL_RGBA32F);
  glBindImageTexture(1, app->path_trace_texture, 0, GL_FALSE, 0, GL_WRITE_ONLY,
                     GL_RGBA8);
  glUniform2i(glGetUniformLocation(app->path_trace_compute_program, "uImageSize"), w, h);
  glUniform1ui(glGetUniformLocation(app->path_trace_compute_program, "uSampleIndex"),
               static_cast<GLuint>(app->path_trace_completed_passes));
  glUniform3f(glGetUniformLocation(app->path_trace_compute_program, "uCameraPos"),
              eye.x, eye.y, eye.z);
  glUniform3f(glGetUniformLocation(app->path_trace_compute_program, "uCameraForward"),
              forward.x, forward.y, forward.z);
  glUniform3f(glGetUniformLocation(app->path_trace_compute_program, "uCameraRight"),
              right.x, right.y, right.z);
  glUniform3f(glGetUniformLocation(app->path_trace_compute_program, "uCameraUp"),
              up.x, up.y, up.z);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uTanHalfFovY"),
              std::tan(kCameraFovYRadians * 0.5f));
  glUniform3f(glGetUniformLocation(app->path_trace_compute_program, "uVolumeMin"),
              gpu_volume.world_bounds.min.x, gpu_volume.world_bounds.min.y,
              gpu_volume.world_bounds.min.z);
  glUniform3f(glGetUniformLocation(app->path_trace_compute_program, "uVolumeMax"),
              gpu_volume.world_bounds.max.x, gpu_volume.world_bounds.max.y,
              gpu_volume.world_bounds.max.z);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uValueOffset"),
              value_offset);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uValueScale"),
              value_scale);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uDensityGain"),
              app->density_gain / std::max(max_extent, 1.0e-4f));
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uValueGamma"),
              app->value_gamma);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uOpacityPower"),
              app->opacity_power);
  glUniform1i(glGetUniformLocation(app->path_trace_compute_program, "uInvertValues"),
              app->invert_values ? 1 : 0);
  glUniform1i(glGetUniformLocation(app->path_trace_compute_program, "uStepCount"),
              std::max(1, std::min(512, app->sample_steps)));
  const float* clip_min = app->clip_enabled ? app->clip_min : nullptr;
  const float* clip_max = app->clip_enabled ? app->clip_max : nullptr;
  glUniform3f(glGetUniformLocation(app->path_trace_compute_program, "uClipMin"),
              clip_min ? clip_min[0] : 0.0f,
              clip_min ? clip_min[1] : 0.0f,
              clip_min ? clip_min[2] : 0.0f);
  glUniform3f(glGetUniformLocation(app->path_trace_compute_program, "uClipMax"),
              clip_max ? clip_max[0] : 1.0f,
              clip_max ? clip_max[1] : 1.0f,
              clip_max ? clip_max[2] : 1.0f);
  glUniform1i(glGetUniformLocation(app->path_trace_compute_program, "uSliceAxis"),
              app->slice_axis);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uSlicePos"),
              app->slice_pos);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uSliceThickness"),
              app->slice_axis ? app->slice_thickness : 1.0f);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uSunElevation"),
              app->path_trace_sun_angle);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uSunAzimuth"),
              app->path_trace_sun_azimuth);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uSunStrength"),
              app->path_trace_sun_strength);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uSkyStrength"),
              app->path_trace_sky_strength);
  glUniform1f(glGetUniformLocation(app->path_trace_compute_program, "uAlbedo"),
              app->path_trace_albedo);
  glDispatchCompute(static_cast<GLuint>((w + 7) / 8), static_cast<GLuint>((h + 7) / 8), 1);
  glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT | GL_TEXTURE_FETCH_BARRIER_BIT);
  ++app->path_trace_completed_passes;
  app->path_trace_next_row = 0;
  app->path_trace_last_backend = "opengl-compute";
  return true;
}

#include "vulkan_pathtrace_backend.inc"

void DrawPathTraceImage(AppState* app) {
  if (!app->path_trace_texture || !app->image_program) return;
  glDisable(GL_DEPTH_TEST);
  glDisable(GL_CULL_FACE);
  glDisable(GL_BLEND);
  glUseProgram(app->image_program);
  glActiveTexture(GL_TEXTURE0);
  glBindTexture(GL_TEXTURE_2D, app->path_trace_texture);
  glUniform1i(glGetUniformLocation(app->image_program, "uImage"), 0);
  glBindVertexArray(app->image_vao);
  glDrawArrays(GL_TRIANGLES, 0, 3);
  glBindVertexArray(0);
  glEnable(GL_DEPTH_TEST);
  glEnable(GL_CULL_FACE);
}

void DrawHud(AppState* app) {
  if (!app->show_hud) return;
  const ImGuiWindowFlags flags =
      ImGuiWindowFlags_NoDecoration | ImGuiWindowFlags_AlwaysAutoResize |
      ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoFocusOnAppearing |
      ImGuiWindowFlags_NoNav | ImGuiWindowFlags_NoInputs;
  ImGui::SetNextWindowPos(ImVec2(10.0f, 10.0f), ImGuiCond_Always);
  ImGui::SetNextWindowBgAlpha(0.35f);
  if (!ImGui::Begin("tvdbview HUD", nullptr, flags)) {
    ImGui::End();
    return;
  }
  ImGui::TextUnformatted("tvdbview");
  if (!app->current_path.empty()) ImGui::Text("file: %s", app->current_path.c_str());
  if (app->active_volume < app->scene.volumes.size()) {
    const VolumeData& v = app->scene.volumes[app->active_volume];
    ImGui::Text("grid: [%zu] %s", app->active_volume, v.name.c_str());
    if (!v.density.empty()) {
      ImGui::Text("dim: %dx%dx%d stride: %d", v.dim[0], v.dim[1], v.dim[2],
                  v.downsample_stride);
      ImGui::Text("range: %.6g .. %.6g", v.min_value, v.max_value);
    } else {
      ImGui::TextUnformatted("topology-only grid");
    }
  }
  ImGui::Text("mode: %s / %s", RenderModeLabel(app->render_mode),
              ColorModeLabel(app->color_mode));
  ImGui::Text("ray: %s iso %.3f", RayModeLabel(app->ray_mode), app->iso_threshold);
  if (app->ray_mode == VolumeRayMode::PathTraceCpu) {
    ImGui::Text("pt: %dx%d pass %d row %d %s", app->path_trace_width,
                app->path_trace_height, app->path_trace_completed_passes,
                app->path_trace_next_row, app->path_trace_last_backend.c_str());
  }
  ImGui::Text("shade: %s %.2f", app->shade_enabled ? "on" : "off",
              app->shade_strength);
  ImGui::Text("gain/steps: %.3f / %d", app->density_gain, app->sample_steps);
  ImGui::Text("window: %.6g .. %.6g%s", app->window_min, app->window_max,
              app->manual_window ? " manual" : "");
  ImGui::Text("gamma/opacity: %.3f / %.3f%s", app->value_gamma, app->opacity_power,
              app->invert_values ? " inverted" : "");
  ImGui::Text("slice: %s pos %.3f width %.4f", SliceAxisLabel(app->slice_axis),
              app->slice_pos, app->slice_thickness);
  ImGui::Text("clip: %s", app->clip_enabled ? "on" : "off");
  if (app->has_probe) {
    ImGui::Text("probe: [%d,%d,%d] %.6g", app->probe_index[0], app->probe_index[1],
                app->probe_index[2], app->probe_value);
  }
  ImGui::End();
}

void DrawControlPanel(AppState* app) {
  if (!app->show_control_panel) return;
  ImGui::SetNextWindowSize(ImVec2(360.0f, 0.0f), ImGuiCond_FirstUseEver);
  if (!ImGui::Begin("tvdbview controls", &app->show_control_panel)) {
    ImGui::End();
    return;
  }

  if (ImGui::Button("Open")) OpenVdbDialog(app);
  ImGui::SameLine();
  if (ImGui::Button("Screenshot")) SaveScreenshot(app);
  ImGui::SameLine();
  if (ImGui::Button("Frame")) FrameSelectedVolume(app);

  if (ImGui::BeginTabBar("tvdbview_tabs")) {
    if (ImGui::BeginTabItem("Scene")) {
  ImGui::SeparatorText("Attribute");
  std::string active_label = "(none)";
  if (app->active_volume < app->scene.volumes.size()) {
    active_label = "[" + std::to_string(app->active_volume) + "] " +
                   app->scene.volumes[app->active_volume].name;
  }
  if (ImGui::BeginCombo("Grid", active_label.c_str())) {
    for (std::size_t i = 0; i < app->scene.volumes.size(); ++i) {
      const VolumeData& v = app->scene.volumes[i];
      std::string label = "[" + std::to_string(i) + "] " + v.name;
      if (v.density.empty()) label += " (topology)";
      const bool selected = (i == app->active_volume);
      if (ImGui::Selectable(label.c_str(), selected)) {
        SelectVolume(app, i);
        UpdateWindowTitle(app);
      }
      if (selected) ImGui::SetItemDefaultFocus();
    }
    ImGui::EndCombo();
  }
  if (app->active_volume < app->scene.volumes.size()) {
    const VolumeData& v = app->scene.volumes[app->active_volume];
    if (!v.density.empty()) {
      ImGui::Text("dim %dx%dx%d, stride %d", v.dim[0], v.dim[1], v.dim[2],
                  v.downsample_stride);
      ImGui::Text("range %.6g .. %.6g", v.min_value, v.max_value);
      ImGui::Text("background %.6g, level set %s", v.background,
                  v.is_level_set ? "yes" : "no");
      ImGui::Text("origin [%d, %d, %d]", v.origin_index[0], v.origin_index[1],
                  v.origin_index[2]);
      ImGui::Text("voxel %.6g %.6g %.6g", v.voxel_size[0], v.voxel_size[1],
                  v.voxel_size[2]);
      ImGui::Text("translate %.6g %.6g %.6g", v.translation[0], v.translation[1],
                  v.translation[2]);
      if (v.world_bounds.valid) {
        ImGui::Text("bounds min %.6g %.6g %.6g", v.world_bounds.min.x,
                    v.world_bounds.min.y, v.world_bounds.min.z);
        ImGui::Text("bounds max %.6g %.6g %.6g", v.world_bounds.max.x,
                    v.world_bounds.max.y, v.world_bounds.max.z);
      }
      ImGui::Text("nodes %zu, max level %d", v.node_boxes.size(), v.max_level);
      if (v.has_active_bbox) {
        ImGui::Text("active index min [%d, %d, %d]", v.active_index_min[0],
                    v.active_index_min[1], v.active_index_min[2]);
        ImGui::Text("active index max [%d, %d, %d]", v.active_index_max[0],
                    v.active_index_max[1], v.active_index_max[2]);
      } else {
        ImGui::TextUnformatted("active index bbox: empty");
      }
      if (!v.emission_name.empty()) ImGui::Text("emission %s", v.emission_name.c_str());
      if (!v.vector_name.empty()) ImGui::Text("vector %s", v.vector_name.c_str());
      ImGui::Text("mean %.6g, non-bg %.2f%%", v.mean_value,
                  v.non_background_fraction * 100.0f);
      ImGui::Text("hist %.6g .. %.6g", v.histogram_min, v.histogram_max);
      if (!v.histogram.empty()) {
        ImGui::PlotHistogram("##histogram", v.histogram.data(),
                             static_cast<int>(v.histogram.size()), 0, nullptr,
                             0.0f, 1.0f, ImVec2(0.0f, 56.0f));
      }
    }
  }

  ImGui::SeparatorText("Reproduce");
  const std::string command_line = BuildCurrentCommandLine(*app);
  if (ImGui::Button("Copy command")) ImGui::SetClipboardText(command_line.c_str());
  ImGui::TextWrapped("%s", command_line.c_str());

  ImGui::SeparatorText("Window");
  ImGui::Text("window %dx%d, framebuffer %dx%d", app->window_width, app->window_height,
              app->framebuffer_width, app->framebuffer_height);
  if (ImGui::Button("Clean capture")) {
    app->show_hud = false;
    app->show_control_panel = false;
  }

      ImGui::EndTabItem();
    }
    if (ImGui::BeginTabItem("Render")) {
  ImGui::SeparatorText("Rendering");
  const char* render_items[] = {"volume", "volume+grid", "grid"};
  int render_mode = static_cast<int>(app->render_mode);
  if (ImGui::Combo("Display", &render_mode, render_items, 3)) {
    app->render_mode = static_cast<VolumeRenderMode>(render_mode);
    UpdateWindowTitle(app);
  }
  const char* color_items[] = {"density", "jet", "blackbody", "vector"};
  int color_mode = static_cast<int>(app->color_mode);
  if (ImGui::Combo("Color", &color_mode, color_items, 4)) {
    app->color_mode = static_cast<VolumeColorMode>(color_mode);
    UpdateWindowTitle(app);
  }
  const char* ray_items[] = {"composite", "mip", "iso", "pathtrace-cpu"};
  int ray_mode = static_cast<int>(app->ray_mode);
  if (ImGui::Combo("Ray mode", &ray_mode, ray_items, 4)) {
    app->ray_mode = static_cast<VolumeRayMode>(ray_mode);
    ResetPathTrace(app);
  }
  ImGui::SliderFloat("Iso threshold", &app->iso_threshold, 0.0f, 1.0f, "%.3f");
  if (app->ray_mode == VolumeRayMode::PathTraceCpu) {
    if (ImGui::SliderInt("PT scale", &app->path_trace_scale, 1, 8)) ResetPathTrace(app);
    const char* pt_backends[] = {"auto", "GL compute", "cpu", "Vulkan compute"};
    if (ImGui::Combo("PT backend", &app->path_trace_backend, pt_backends, 4)) {
      ResetPathTrace(app);
    }
    if (ImGui::SliderInt("PT rows/frame", &app->path_trace_rows_per_frame, 1, 256)) {
      app->path_trace_rows_per_frame = std::max(1, app->path_trace_rows_per_frame);
    }
    if (ImGui::SliderInt("PT depth", &app->path_trace_max_depth, 1, 8)) ResetPathTrace(app);
    if (ImGui::SliderFloat("Sun elevation", &app->path_trace_sun_angle, -5.0f, 89.0f,
                           "%.1f")) {
      ResetPathTrace(app);
    }
    if (ImGui::SliderFloat("Sun azimuth", &app->path_trace_sun_azimuth, -180.0f, 180.0f,
                           "%.1f")) {
      ResetPathTrace(app);
    }
    if (ImGui::SliderFloat("Sun strength", &app->path_trace_sun_strength, 0.0f, 20.0f,
                           "%.2f")) {
      ResetPathTrace(app);
    }
    if (ImGui::SliderFloat("Sky strength", &app->path_trace_sky_strength, 0.0f, 5.0f,
                           "%.2f")) {
      ResetPathTrace(app);
    }
    if (ImGui::SliderFloat("PT albedo", &app->path_trace_albedo, 0.0f, 1.0f, "%.2f")) {
      ResetPathTrace(app);
    }
    ImGui::Text("PT pass %d, row %d/%d", app->path_trace_completed_passes,
                app->path_trace_next_row, std::max(app->path_trace_height, 1));
    ImGui::Text("accumulation: %s",
                (app->path_trace_completed_passes == 0 &&
                 app->path_trace_next_row == 0)
                    ? "reset"
                    : "progressive");
    ImGui::Text("last backend: %s", app->path_trace_last_backend.c_str());
    ImGui::SliderInt("Capture SPP", &app->path_trace_capture_samples, 0, 512);
    ImGui::Text("compute backend: %s",
                app->path_trace_compute_available ? "available" : "unavailable");
    ImGui::Text("vulkan backend: %s",
                app->path_trace_vulkan_available ? "available" : "runtime/disabled");
    if (ImGui::Button("Reset PT")) ResetPathTrace(app);
    ImGui::SameLine();
    if (ImGui::Button("Save PT PNG")) SavePathTraceImage(app);
  }
  ImGui::Checkbox("Gradient shading", &app->shade_enabled);
  ImGui::SliderFloat("Shade strength", &app->shade_strength, 0.0f, 1.0f, "%.3f");
  if (ImGui::SliderFloat3("Light dir", &app->light_dir.x, -1.0f, 1.0f, "%.3f")) {
    app->light_dir = Normalize(app->light_dir);
  }
  ImGui::SliderFloat("Density gain", &app->density_gain, 0.05f, 200.0f, "%.3f",
                     ImGuiSliderFlags_Logarithmic);
  const float data_span = std::max(std::fabs(app->window_max - app->window_min), 1.0f);
  bool manual_window = app->manual_window;
  if (ImGui::Checkbox("Manual value window", &manual_window)) {
    app->manual_window = manual_window;
    if (!app->manual_window) ResetValueWindow(app);
  }
  ImGui::BeginDisabled(!app->manual_window);
  if (ImGui::DragFloatRange2("Value min/max", &app->window_min, &app->window_max,
                             data_span / 200.0f, -FLT_MAX, FLT_MAX, "%.6g", "%.6g")) {
    ClampValueWindow(app);
  }
  ImGui::EndDisabled();
  ImGui::SameLine();
  if (ImGui::Button("Reset##value_window")) ResetValueWindow(app);
  if (ImGui::Button("Auto 1-99%")) SetPercentileValueWindow(app, 1.0f, 99.0f);
  ImGui::SameLine();
  if (ImGui::Button("Auto 5-95%")) SetPercentileValueWindow(app, 5.0f, 95.0f);
  ImGui::SliderFloat("Value gamma", &app->value_gamma, 0.1f, 5.0f, "%.3f",
                     ImGuiSliderFlags_Logarithmic);
  ImGui::SliderFloat("Opacity power", &app->opacity_power, 0.1f, 5.0f, "%.3f",
                     ImGuiSliderFlags_Logarithmic);
  ImGui::Checkbox("Invert values", &app->invert_values);
  ImGui::SliderInt("Ray steps", &app->sample_steps, 16, 512);
  ImGui::Checkbox("SDF fog", &app->sdf_fog_mode);
  ImGui::Checkbox("HUD", &app->show_hud);

  ImGui::SeparatorText("Slice / Clip");
  const char* slice_items[] = {"off", "x", "y", "z"};
  ImGui::Combo("Slice axis", &app->slice_axis, slice_items, 4);
  ImGui::SliderFloat("Slice position", &app->slice_pos, 0.0f, 1.0f, "%.3f");
  ImGui::SliderFloat("Slice thickness", &app->slice_thickness, 0.0025f, 1.0f, "%.4f",
                     ImGuiSliderFlags_Logarithmic);
  ImGui::Checkbox("Clip box", &app->clip_enabled);
  if (app->clip_enabled) {
    if (ImGui::SliderFloat3("Clip min", app->clip_min, 0.0f, 1.0f, "%.3f")) {
      ClampClipBox(app);
    }
    if (ImGui::SliderFloat3("Clip max", app->clip_max, 0.0f, 1.0f, "%.3f")) {
      ClampClipBox(app);
    }
  }
  if (ImGui::Button("Clip active")) SetClipToActiveBounds(app);
  ImGui::SameLine();
  if (ImGui::Button("Full clip")) {
    app->clip_enabled = false;
    app->clip_min[0] = app->clip_min[1] = app->clip_min[2] = 0.0f;
    app->clip_max[0] = app->clip_max[1] = app->clip_max[2] = 1.0f;
  }

  ImGui::SeparatorText("Bounding Boxes");
  ImGui::Checkbox("Dense bounds", &app->show_dense_bounds);
  ImGui::Checkbox("Internal nodes", &app->show_internal_boxes);
  ImGui::Checkbox("Leaf nodes", &app->show_leaf_boxes);

      ImGui::EndTabItem();
    }
    if (ImGui::BeginTabItem("Probe")) {
  ImGui::SeparatorText("Probe");
  const char* probe_modes[] = {"midpoint", "max visible"};
  ImGui::Combo("Probe mode", &app->probe_mode, probe_modes, 2);
  if (app->has_probe) {
    ImGui::Text("index [%d, %d, %d]", app->probe_index[0], app->probe_index[1],
                app->probe_index[2]);
    ImGui::Text("value %.9g", app->probe_value);
    ImGui::Text("uvw %.4f %.4f %.4f", app->probe_uvw.x, app->probe_uvw.y,
                app->probe_uvw.z);
    ImGui::Text("world %.4f %.4f %.4f", app->probe_world.x, app->probe_world.y,
                app->probe_world.z);
  } else {
    ImGui::TextUnformatted("Ctrl+left click inside the volume.");
  }

      ImGui::EndTabItem();
    }
    if (ImGui::BeginTabItem("Camera")) {
  ImGui::SeparatorText("Camera");
  if (ImGui::Button("Front")) SetCameraPreset(app, 0);
  ImGui::SameLine();
  if (ImGui::Button("Top")) SetCameraPreset(app, 1);
  ImGui::SameLine();
  if (ImGui::Button("Side")) SetCameraPreset(app, 2);
  for (int i = 0; i < 3; ++i) {
    char save_label[32];
    char load_label[32];
    std::snprintf(save_label, sizeof(save_label), "Save %d", i + 1);
    std::snprintf(load_label, sizeof(load_label), "Load %d", i + 1);
    if (i > 0) ImGui::SameLine();
    if (ImGui::Button(save_label)) {
      app->camera_bookmarks[i] = app->camera;
      app->has_camera_bookmark[i] = true;
    }
    ImGui::SameLine();
    ImGui::BeginDisabled(!app->has_camera_bookmark[i]);
    if (ImGui::Button(load_label)) app->camera = app->camera_bookmarks[i];
    ImGui::EndDisabled();
  }

      ImGui::EndTabItem();
    }
    ImGui::EndTabBar();
  }

  ImGui::End();
}

void DrawImGui(AppState* app) {
  ImGui_ImplOpenGL3_NewFrame();
  ImGui_ImplGlfw_NewFrame();
  ImGui::NewFrame();
  DrawHud(app);
  DrawControlPanel(app);
  ImGui::Render();
  ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());
}

void Draw(AppState* app) {
  glViewport(0, 0, app->framebuffer_width, app->framebuffer_height);
  glClearColor(0.02f, 0.025f, 0.03f, 1.0f);
  glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

  const float aspect =
      app->framebuffer_height > 0
          ? static_cast<float>(app->framebuffer_width) /
                static_cast<float>(app->framebuffer_height)
          : 1.0f;
  const Mat4 vp = app->camera.viewProjection(aspect);
  const Vec3 eye = app->camera.eye();
  const bool draw_density = app->render_mode != VolumeRenderMode::GridOnly;
  const bool draw_grid = app->render_mode != VolumeRenderMode::Volume;
  const bool draw_path_trace = draw_density && app->ray_mode == VolumeRayMode::PathTraceCpu;

  if (draw_path_trace) {
    bool rendered = false;
    if (app->path_trace_backend == 3 || app->path_trace_backend == 0) {
      rendered = UpdatePathTraceVulkan(app);
    }
    if (!rendered && (app->path_trace_backend == 1 || app->path_trace_backend == 0)) {
      rendered = UpdatePathTraceCompute(app);
    }
    if (!rendered) UpdatePathTraceCpu(app);
    DrawPathTraceImage(app);
  } else if (draw_density) {
    glEnable(GL_BLEND);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glDisable(GL_CULL_FACE);
    glDepthMask(GL_FALSE);
    glUseProgram(app->volume_program);
    if (app->active_volume < app->gpu_volumes.size()) {
      const GpuVolume& volume = app->gpu_volumes[app->active_volume];
      if (volume.world_bounds.valid && volume.has_density) {
        const Vec3 mn = volume.world_bounds.min;
        const Vec3 ex = volume.world_bounds.max - volume.world_bounds.min;
        Mat4 model = Mat4::Identity();
        model.at(0, 0) = ex.x;
        model.at(1, 1) = ex.y;
        model.at(2, 2) = ex.z;
        model.at(3, 0) = mn.x;
        model.at(3, 1) = mn.y;
        model.at(3, 2) = mn.z;
        SetMat4(app->volume_program, "uModel", model);
        SetMat4(app->volume_program, "uVP", vp);
        glUniform3f(glGetUniformLocation(app->volume_program, "uCameraPos"),
                    eye.x, eye.y, eye.z);
        glUniform3f(glGetUniformLocation(app->volume_program, "uVolumeMin"),
                    volume.world_bounds.min.x, volume.world_bounds.min.y,
                    volume.world_bounds.min.z);
        glUniform3f(glGetUniformLocation(app->volume_program, "uVolumeMax"),
                    volume.world_bounds.max.x, volume.world_bounds.max.y,
                    volume.world_bounds.max.z);
        float value_offset = volume.value_offset;
        float value_scale = volume.value_scale;
        if (app->manual_window) {
          ClampValueWindow(app);
          const float value_range = app->window_max - app->window_min;
          value_offset = app->window_min;
          value_scale = value_range > 1.0e-8f ? 1.0f / value_range : 1.0f;
        }
        glUniform1f(glGetUniformLocation(app->volume_program, "uValueOffset"),
                    value_offset);
        glUniform1f(glGetUniformLocation(app->volume_program, "uValueScale"),
                    value_scale);
        const float max_extent = std::max(ex.x, std::max(ex.y, ex.z));
        glUniform1f(glGetUniformLocation(app->volume_program, "uDensityGain"),
                    app->density_gain / std::max(max_extent, 1.0e-4f));
        glUniform1f(glGetUniformLocation(app->volume_program, "uValueGamma"),
                    app->value_gamma);
        glUniform1f(glGetUniformLocation(app->volume_program, "uOpacityPower"),
                    app->opacity_power);
        glUniform1i(glGetUniformLocation(app->volume_program, "uInvertValues"),
                    app->invert_values ? 1 : 0);
        glUniform1i(glGetUniformLocation(app->volume_program, "uStepCount"),
                    std::max(1, std::min(512, app->sample_steps)));
        glUniform1i(glGetUniformLocation(app->volume_program, "uRayMode"),
                    static_cast<int>(app->ray_mode));
        glUniform1f(glGetUniformLocation(app->volume_program, "uIsoThreshold"),
                    app->iso_threshold);
        glUniform1i(glGetUniformLocation(app->volume_program, "uShadeEnabled"),
                    app->shade_enabled ? 1 : 0);
        glUniform1f(glGetUniformLocation(app->volume_program, "uShadeStrength"),
                    app->shade_strength);
        const Vec3 light_dir = Normalize(app->light_dir);
        glUniform3f(glGetUniformLocation(app->volume_program, "uLightDir"),
                    light_dir.x, light_dir.y, light_dir.z);
        if (app->active_volume < app->scene.volumes.size()) {
          const VolumeData& volume_data = app->scene.volumes[app->active_volume];
          glUniform3f(glGetUniformLocation(app->volume_program, "uTexelSize"),
                      volume_data.dim[0] > 0 ? 1.0f / volume_data.dim[0] : 1.0f,
                      volume_data.dim[1] > 0 ? 1.0f / volume_data.dim[1] : 1.0f,
                      volume_data.dim[2] > 0 ? 1.0f / volume_data.dim[2] : 1.0f);
        }
        glUniform1i(glGetUniformLocation(app->volume_program, "uFogFromSdf"),
                    app->sdf_fog_mode ? 1 : 0);
        glUniform1f(glGetUniformLocation(app->volume_program, "uSdfBandScale"),
                    volume.sdf_band_scale);
        glUniform1i(glGetUniformLocation(app->volume_program, "uColorMode"),
                    static_cast<int>(app->color_mode));
        const float* clip_min = app->clip_enabled ? app->clip_min : nullptr;
        const float* clip_max = app->clip_enabled ? app->clip_max : nullptr;
        glUniform3f(glGetUniformLocation(app->volume_program, "uClipMin"),
                    clip_min ? clip_min[0] : 0.0f,
                    clip_min ? clip_min[1] : 0.0f,
                    clip_min ? clip_min[2] : 0.0f);
        glUniform3f(glGetUniformLocation(app->volume_program, "uClipMax"),
                    clip_max ? clip_max[0] : 1.0f,
                    clip_max ? clip_max[1] : 1.0f,
                    clip_max ? clip_max[2] : 1.0f);
        glUniform1i(glGetUniformLocation(app->volume_program, "uSliceAxis"),
                    app->slice_axis);
        glUniform1f(glGetUniformLocation(app->volume_program, "uSlicePos"),
                    app->slice_pos);
        glUniform1f(glGetUniformLocation(app->volume_program, "uSliceThickness"),
                    app->slice_axis ? app->slice_thickness : 1.0f);

        glActiveTexture(GL_TEXTURE0);
        glBindTexture(GL_TEXTURE_3D, volume.texture);
        glUniform1i(glGetUniformLocation(app->volume_program, "uVolume"), 0);
        glUniform1i(glGetUniformLocation(app->volume_program, "uHasEmission"),
                    volume.has_emission ? 1 : 0);
        glUniform1f(glGetUniformLocation(app->volume_program, "uEmissionOffset"),
                    volume.emission_offset);
        glUniform1f(glGetUniformLocation(app->volume_program, "uEmissionScale"),
                    volume.emission_scale);
        if (volume.has_emission) {
          glActiveTexture(GL_TEXTURE1);
          glBindTexture(GL_TEXTURE_3D, volume.emission_texture);
          glUniform1i(glGetUniformLocation(app->volume_program, "uEmission"), 1);
        }
        glUniform1i(glGetUniformLocation(app->volume_program, "uHasVector"),
                    volume.has_vector ? 1 : 0);
        glUniform1f(glGetUniformLocation(app->volume_program, "uVectorLenScale"),
                    volume.vector_len_scale);
        if (volume.has_vector) {
          glActiveTexture(GL_TEXTURE2);
          glBindTexture(GL_TEXTURE_3D, volume.vector_texture);
          glUniform1i(glGetUniformLocation(app->volume_program, "uVectorTex"), 2);
        }

        glActiveTexture(GL_TEXTURE0);
        glBindVertexArray(volume.vao);
        glDrawElements(GL_TRIANGLES, volume.index_count, GL_UNSIGNED_INT, nullptr);
      }
    }
    glDepthMask(GL_TRUE);
    glEnable(GL_CULL_FACE);
    glDisable(GL_BLEND);
  }

  if (draw_grid) {
    glUseProgram(app->line_program);
    SetMat4(app->line_program, "uVP", vp);
    if (app->active_volume < app->gpu_volumes.size()) {
      const GpuVolume& volume = app->gpu_volumes[app->active_volume];
      auto draw_lines = [](const LineMesh& lines) {
        if (lines.index_count == 0) return;
        glBindVertexArray(lines.vao);
        glDrawElements(GL_LINES, lines.index_count, GL_UNSIGNED_INT, nullptr);
      };
      if (app->show_dense_bounds) draw_lines(volume.dense_bounds_lines);
      if (app->show_internal_boxes) draw_lines(volume.internal_lines);
      if (app->show_leaf_boxes) draw_lines(volume.leaf_lines);
      if (app->slice_axis > 0) {
        LineMesh slice = BuildSliceLineMesh(volume.world_bounds, app->slice_axis, app->slice_pos);
        draw_lines(slice);
        DestroyLineMesh(&slice);
      }
    }
  }

  glBindVertexArray(0);
  DrawImGui(app);
}

AppState* GetApp(GLFWwindow* window) {
  return reinterpret_cast<AppState*>(glfwGetWindowUserPointer(window));
}

void FramebufferSizeCallback(GLFWwindow* window, int width, int height) {
  AppState* app = GetApp(window);
  app->window_width = std::max(width, 1);
  app->window_height = std::max(height, 1);
  app->framebuffer_width = std::max(width, 1);
  app->framebuffer_height = std::max(height, 1);
}

void CursorPosCallback(GLFWwindow* window, double x, double y) {
  AppState* app = GetApp(window);
  const double dx = x - app->last_cursor_x;
  const double dy = y - app->last_cursor_y;
  app->last_cursor_x = x;
  app->last_cursor_y = y;
  if (ImGui::GetCurrentContext() && ImGui::GetIO().WantCaptureMouse) return;

  if (app->left_mouse_down) {
    app->camera.longitude += static_cast<float>(dx) * 0.35f;
    app->camera.latitude += static_cast<float>(dy) * 0.35f;
    app->camera.latitude = std::max(-89.0f, std::min(89.0f, app->camera.latitude));
  } else if (app->middle_mouse_down || app->right_mouse_down) {
    Vec3 right;
    Vec3 up;
    app->camera.localAxes(&right, &up);
    const float scale = app->camera.distance * 0.0015f;
    app->camera.target = app->camera.target - right * static_cast<float>(dx * scale) +
                         up * static_cast<float>(dy * scale);
  }
}

void MouseButtonCallback(GLFWwindow* window, int button, int action, int mods) {
  AppState* app = GetApp(window);
  if (ImGui::GetCurrentContext() && ImGui::GetIO().WantCaptureMouse) {
    glfwGetCursorPos(window, &app->last_cursor_x, &app->last_cursor_y);
    return;
  }
  double x = 0.0;
  double y = 0.0;
  glfwGetCursorPos(window, &x, &y);
  if (button == GLFW_MOUSE_BUTTON_LEFT && action == GLFW_PRESS &&
      (mods & GLFW_MOD_CONTROL)) {
    ProbeAtCursor(app, x, y);
    app->left_mouse_down = false;
    app->last_cursor_x = x;
    app->last_cursor_y = y;
    return;
  }
  if (button == GLFW_MOUSE_BUTTON_LEFT) app->left_mouse_down = action == GLFW_PRESS;
  if (button == GLFW_MOUSE_BUTTON_MIDDLE) app->middle_mouse_down = action == GLFW_PRESS;
  if (button == GLFW_MOUSE_BUTTON_RIGHT) app->right_mouse_down = action == GLFW_PRESS;
  app->last_cursor_x = x;
  app->last_cursor_y = y;
}

void ScrollCallback(GLFWwindow* window, double, double yoffset) {
  AppState* app = GetApp(window);
  if (ImGui::GetCurrentContext() && ImGui::GetIO().WantCaptureMouse) return;
  app->camera.distance *= std::pow(0.88f, static_cast<float>(yoffset));
  app->camera.distance = std::max(app->camera.distance, 0.01f);
}

void KeyCallback(GLFWwindow* window, int key, int, int action, int mods) {
  if (action != GLFW_PRESS) return;
  AppState* app = GetApp(window);
  if (ImGui::GetCurrentContext() && ImGui::GetIO().WantCaptureKeyboard &&
      key != GLFW_KEY_ESCAPE) {
    return;
  }
  if (key >= GLFW_KEY_F1 && key <= GLFW_KEY_F3) {
    const int idx = key - GLFW_KEY_F1;
    if (mods & GLFW_MOD_CONTROL) {
      app->camera_bookmarks[idx] = app->camera;
      app->has_camera_bookmark[idx] = true;
      std::cout << "saved camera bookmark " << (idx + 1) << "\n";
    } else if (mods & GLFW_MOD_SHIFT) {
      if (app->has_camera_bookmark[idx]) {
        app->camera = app->camera_bookmarks[idx];
        std::cout << "loaded camera bookmark " << (idx + 1) << "\n";
      } else {
        std::cerr << "camera bookmark " << (idx + 1) << " is empty\n";
      }
    } else {
      SetCameraPreset(app, idx);
    }
    return;
  }
  switch (key) {
    case GLFW_KEY_ESCAPE:
      glfwSetWindowShouldClose(window, GLFW_TRUE);
      break;
    case GLFW_KEY_H:
      PrintControls();
      PrintVolumeList(*app);
      break;
    case GLFW_KEY_O:
      OpenVdbDialog(app);
      UpdateWindowTitle(app);
      break;
    case GLFW_KEY_X:
      app->slice_axis = 1;
      app->slice_thickness = std::min(app->slice_thickness, 0.04f);
      std::cout << "slice axis: x\n";
      break;
    case GLFW_KEY_Y:
      app->slice_axis = 2;
      app->slice_thickness = std::min(app->slice_thickness, 0.04f);
      std::cout << "slice axis: y\n";
      break;
    case GLFW_KEY_Z:
      app->slice_axis = 3;
      app->slice_thickness = std::min(app->slice_thickness, 0.04f);
      std::cout << "slice axis: z\n";
      break;
    case GLFW_KEY_BACKSLASH:
      app->slice_axis = 0;
      app->slice_thickness = 1.0f;
      std::cout << "slice: off\n";
      break;
    case GLFW_KEY_COMMA:
      app->slice_pos = std::max(0.0f, app->slice_pos - 0.025f);
      std::cout << "slice position: " << app->slice_pos << "\n";
      break;
    case GLFW_KEY_PERIOD:
      app->slice_pos = std::min(1.0f, app->slice_pos + 0.025f);
      std::cout << "slice position: " << app->slice_pos << "\n";
      break;
    case GLFW_KEY_MINUS:
      app->slice_thickness = std::max(0.0025f, app->slice_thickness * 0.75f);
      std::cout << "slice thickness: " << app->slice_thickness << "\n";
      break;
    case GLFW_KEY_EQUAL:
      app->slice_thickness = std::min(1.0f, app->slice_thickness * 1.3333334f);
      std::cout << "slice thickness: " << app->slice_thickness << "\n";
      break;
    case GLFW_KEY_K:
      app->clip_enabled = !app->clip_enabled;
      if (app->clip_enabled) {
        app->clip_min[0] = app->clip_min[1] = app->clip_min[2] = 0.1f;
        app->clip_max[0] = app->clip_max[1] = app->clip_max[2] = 0.9f;
      }
      std::cout << "clip box: " << (app->clip_enabled ? "on" : "off") << "\n";
      break;
    case GLFW_KEY_U:
      AdjustClipBox(app, 0.05f);
      break;
    case GLFW_KEY_J:
      AdjustClipBox(app, -0.05f);
      break;
    case GLFW_KEY_I:
      app->show_internal_boxes = !app->show_internal_boxes;
      std::cout << "internal boxes: " << (app->show_internal_boxes ? "on" : "off") << "\n";
      break;
    case GLFW_KEY_L:
      app->show_leaf_boxes = !app->show_leaf_boxes;
      std::cout << "leaf boxes: " << (app->show_leaf_boxes ? "on" : "off") << "\n";
      break;
    case GLFW_KEY_B:
      app->show_dense_bounds = !app->show_dense_bounds;
      std::cout << "dense bounds: " << (app->show_dense_bounds ? "on" : "off") << "\n";
      break;
    case GLFW_KEY_V:
      app->render_mode = NextRenderMode(app->render_mode);
      std::cout << "render mode: " << RenderModeLabel(app->render_mode) << "\n";
      UpdateWindowTitle(app);
      break;
    case GLFW_KEY_C:
      app->color_mode = NextColorMode(app->color_mode);
      std::cout << "color mode: " << ColorModeLabel(app->color_mode) << "\n";
      UpdateWindowTitle(app);
      break;
    case GLFW_KEY_M:
      app->ray_mode = NextRayMode(app->ray_mode);
      ResetPathTrace(app);
      std::cout << "ray mode: " << RayModeLabel(app->ray_mode) << "\n";
      break;
    case GLFW_KEY_P:
      Draw(app);
      SaveScreenshot(app);
      break;
    case GLFW_KEY_LEFT_BRACKET:
      app->density_gain = std::max(0.05f, app->density_gain / 1.3f);
      std::cout << "density gain: " << app->density_gain << "\n";
      break;
    case GLFW_KEY_RIGHT_BRACKET:
      app->density_gain = std::min(200.0f, app->density_gain * 1.3f);
      std::cout << "density gain: " << app->density_gain << "\n";
      break;
    case GLFW_KEY_S:
      app->sdf_fog_mode = !app->sdf_fog_mode;
      std::cout << "SDF fog mode: " << (app->sdf_fog_mode ? "on" : "off") << "\n";
      break;
    case GLFW_KEY_R:
      app->camera.resetToBounds(app->scene.bounds);
      break;
    case GLFW_KEY_F:
      FrameSelectedVolume(app);
      break;
    default:
      if (key >= GLFW_KEY_0 && key <= GLFW_KEY_9) {
        const std::size_t index = static_cast<std::size_t>(key - GLFW_KEY_0);
        if (SelectVolume(app, index)) UpdateWindowTitle(app);
      }
      break;
  }
}

bool InitGlfwAndGl(AppState* app) {
  if (!glfwInit()) {
    std::cerr << "Failed to initialize GLFW.\n";
    return false;
  }
  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 3);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 3);
  glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
#if defined(__APPLE__)
  glfwWindowHint(GLFW_OPENGL_FORWARD_COMPAT, GLFW_TRUE);
#endif

  app->window = glfwCreateWindow(app->window_width, app->window_height,
                                 "tvdbview", nullptr, nullptr);
  if (!app->window) {
    std::cerr << "Failed to create GLFW window.\n";
    glfwTerminate();
    return false;
  }
  glfwMakeContextCurrent(app->window);
  glfwSwapInterval(1);
  glfwSetWindowUserPointer(app->window, app);
  glfwSetFramebufferSizeCallback(app->window, FramebufferSizeCallback);
  glfwSetCursorPosCallback(app->window, CursorPosCallback);
  glfwSetMouseButtonCallback(app->window, MouseButtonCallback);
  glfwSetScrollCallback(app->window, ScrollCallback);
  glfwSetKeyCallback(app->window, KeyCallback);
  glfwGetFramebufferSize(app->window, &app->framebuffer_width, &app->framebuffer_height);

  if (!gladLoadGLLoader(reinterpret_cast<GLADloadproc>(glfwGetProcAddress))) {
    std::cerr << "Failed to load OpenGL symbols.\n";
    return false;
  }
  std::cout << "OpenGL: " << glGetString(GL_VERSION) << "\n";

  app->volume_program = CreateProgram(kVolumeVs, kVolumeFs);
  app->line_program = CreateProgram(kLineVs, kLineFs);
  app->image_program = CreateProgram(kImageVs, kImageFs);
  if (!app->volume_program || !app->line_program || !app->image_program) {
    return false;
  }
  if (GLAD_GL_VERSION_4_3) {
    app->path_trace_compute_program = CreateComputeProgram(kPathTraceCs);
    app->path_trace_compute_available = app->path_trace_compute_program != 0;
  }
  if (!app->path_trace_compute_available) {
    std::cout << "Path trace compute backend unavailable; CPU progressive fallback enabled.\n";
  }
  glGenVertexArrays(1, &app->image_vao);

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImGui::StyleColorsDark();
  ImGui_ImplGlfw_InitForOpenGL(app->window, true);
  ImGui_ImplOpenGL3_Init("#version 330 core");

  glEnable(GL_DEPTH_TEST);
  glEnable(GL_CULL_FACE);
  glLineWidth(1.0f);
  return true;
}

void Shutdown(AppState* app) {
  DestroyVulkanPathTrace(app);
  ClearGpuVolumes(app);
  if (ImGui::GetCurrentContext()) {
    ImGui_ImplOpenGL3_Shutdown();
    ImGui_ImplGlfw_Shutdown();
    ImGui::DestroyContext();
  }
  if (app->volume_program) glDeleteProgram(app->volume_program);
  if (app->line_program) glDeleteProgram(app->line_program);
  if (app->image_program) glDeleteProgram(app->image_program);
  if (app->path_trace_compute_program) glDeleteProgram(app->path_trace_compute_program);
  if (app->image_vao) glDeleteVertexArrays(1, &app->image_vao);
  if (app->path_trace_texture) glDeleteTextures(1, &app->path_trace_texture);
  if (app->path_trace_accum_texture) glDeleteTextures(1, &app->path_trace_accum_texture);
#if defined(TVDBVIEW_ENABLE_NFD)
  if (app->nfd_initialized) NFD_Quit();
#endif
  if (app->window) glfwDestroyWindow(app->window);
  glfwTerminate();
}

}  // namespace

int main(int argc, char** argv) {
  CliOptions cli;
  if (!ParseCli(argc, argv, &cli)) {
    PrintUsage(argv[0]);
    return EXIT_FAILURE;
  }
  if (cli.show_help) {
    PrintUsage(argv[0]);
    return EXIT_SUCCESS;
  }

  AppState app;
  if (cli.has_window_size) {
    app.window_width = cli.window_width;
    app.window_height = cli.window_height;
    app.framebuffer_width = cli.window_width;
    app.framebuffer_height = cli.window_height;
  }
  if (!InitGlfwAndGl(&app)) {
    Shutdown(&app);
    return EXIT_FAILURE;
  }

  PrintControls();
  if (!cli.input_path.empty()) {
    if (!LoadSceneIntoApp(&app, cli.input_path) || !ApplyCliOptionsAfterLoad(&app, cli)) {
      Shutdown(&app);
      return EXIT_FAILURE;
    }
  } else {
    app.camera.resetToBounds(app.scene.bounds);
    std::cout << "No input file. Press O to open a .vdb file.\n";
  }
  UpdateWindowTitle(&app);

  while (!glfwWindowShouldClose(app.window)) {
    glfwPollEvents();
    Draw(&app);
    const bool wait_for_path_trace =
        app.pending_capture && app.ray_mode == VolumeRayMode::PathTraceCpu &&
        app.path_trace_capture_samples > 0 &&
        app.path_trace_completed_passes < app.path_trace_capture_samples;
    if (app.pending_capture && !wait_for_path_trace) {
      if (app.ray_mode == VolumeRayMode::PathTraceCpu && app.show_hud == false &&
          app.show_control_panel == false && !app.path_trace_rgba.empty()) {
        SavePathTraceImage(&app, app.capture_path);
      } else {
        SaveScreenshot(&app, app.capture_path);
      }
      app.pending_capture = false;
      if (app.quit_after_capture) glfwSetWindowShouldClose(app.window, GLFW_TRUE);
    }
    glfwSwapBuffers(app.window);
  }

  Shutdown(&app);
  return EXIT_SUCCESS;
}
