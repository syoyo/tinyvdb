#include <glad/glad.h>
#include <GLFW/glfw3.h>

#if defined(TVDBVIEW_ENABLE_NFD)
#include <nfd.h>
#endif

#include "tinyvdb_io.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <limits>
#include <string>
#include <utility>
#include <vector>

namespace {

const int kWindowWidth = 1280;
const int kWindowHeight = 900;
const std::size_t kMaxDenseVoxels = 256ull * 256ull * 256ull;

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
    const Mat4 proj = Perspective(45.0f * 3.1415926535f / 180.0f, aspect, 0.01f, far_plane);
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
  LineMesh grid_lines;
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

struct AppState {
  GLFWwindow* window = nullptr;
  int framebuffer_width = kWindowWidth;
  int framebuffer_height = kWindowHeight;
  GLuint volume_program = 0;
  GLuint line_program = 0;
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
  float density_gain = 2.0f;
  bool sdf_fog_mode = false;
  std::string current_path;
#if defined(TVDBVIEW_ENABLE_NFD)
  bool nfd_initialized = false;
#endif
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
uniform int uFogFromSdf;
uniform float uSdfBandScale;
uniform int uColorMode;

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

  const int kSteps = 128;
  float dt = (tExit - tEnter) / float(kSteps);
  float transmittance = 1.0;
  vec3 accumColor = vec3(0.0);
  vec3 extent = uVolumeMax - uVolumeMin;
  for (int i = 0; i < kSteps; ++i) {
    float t = tEnter + (float(i) + 0.5) * dt;
    vec3 p = ro + rd * t;
    vec3 uvw = (p - uVolumeMin) / extent;
    float raw = texture(uVolume, uvw).r;
    float norm = (uFogFromSdf == 1)
        ? clamp(-raw * uSdfBandScale, 0.0, 1.0)
        : clamp((raw - uValueOffset) * uValueScale, 0.0, 1.0);
    float density = norm * uDensityGain;
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

    float alpha = 1.0 - exp(-density * dt);
    accumColor += transmittance * alpha * sampleColor;
    transmittance *= (1.0 - alpha);
    if (transmittance < 0.005) break;
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

VolumeColorMode NextColorMode(VolumeColorMode mode) {
  switch (mode) {
    case VolumeColorMode::Density: return VolumeColorMode::Jet;
    case VolumeColorMode::Jet: return VolumeColorMode::Blackbody;
    case VolumeColorMode::Blackbody: return VolumeColorMode::Vector;
    case VolumeColorMode::Vector: return VolumeColorMode::Density;
  }
  return VolumeColorMode::Density;
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
      << "  O                open VDB\n"
      << "  V                cycle volume/grid display\n"
      << "  C                cycle color mode\n"
      << "  [ / ]            density gain down/up\n"
      << "  S                toggle SDF fog mode\n"
      << "  R                reset camera\n"
      << "  H                print controls\n"
      << "  Esc              quit\n";
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
          handled[j] = true;
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

LineMesh BuildVolumeGridLineMesh(const VolumeData& volume) {
  std::vector<float> vertices;
  std::vector<uint32_t> indices;
  vertices.reserve(volume.node_boxes.size() * 8 * 6);
  indices.reserve(volume.node_boxes.size() * 24);
  const int max_level = std::max(volume.max_level, 1);
  static const uint32_t edge_offsets[24] = {
      0, 1, 1, 2, 2, 3, 3, 0,
      4, 5, 5, 6, 6, 7, 7, 4,
      0, 4, 1, 5, 2, 6, 3, 7};

  for (std::size_t b = 0; b < volume.node_boxes.size(); ++b) {
    const VolumeNodeBox& box = volume.node_boxes[b];
    const float t = static_cast<float>(box.level) / static_cast<float>(max_level);
    const Vec3 color{1.0f - t, 0.2f + 0.8f * t, 0.25f + 0.6f * (1.0f - t)};
    const Vec3 mn = box.min;
    const Vec3 mx = box.max;
    const Vec3 corners[8] = {
        {mn.x, mn.y, mn.z}, {mx.x, mn.y, mn.z}, {mx.x, mx.y, mn.z}, {mn.x, mx.y, mn.z},
        {mn.x, mn.y, mx.z}, {mx.x, mn.y, mx.z}, {mx.x, mx.y, mx.z}, {mn.x, mx.y, mx.z}};
    const uint32_t base = static_cast<uint32_t>(vertices.size() / 6);
    for (int c = 0; c < 8; ++c) {
      vertices.push_back(corners[c].x);
      vertices.push_back(corners[c].y);
      vertices.push_back(corners[c].z);
      vertices.push_back(color.x);
      vertices.push_back(color.y);
      vertices.push_back(color.z);
    }
    for (int e = 0; e < 24; ++e) indices.push_back(base + edge_offsets[e]);
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

  gpu.grid_lines = BuildVolumeGridLineMesh(volume);
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
  DestroyLineMesh(&volume->grid_lines);
  *volume = GpuVolume{};
}

void ClearGpuVolumes(AppState* app) {
  for (std::size_t i = 0; i < app->gpu_volumes.size(); ++i) {
    DestroyVolume(&app->gpu_volumes[i]);
  }
  app->gpu_volumes.clear();
}

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
  app->camera.resetToBounds(app->scene.bounds);
  app->current_path = path;
  if (!app->scene.volumes.empty()) {
    bool has_density = false;
    for (std::size_t i = 0; i < app->gpu_volumes.size(); ++i) {
      has_density = has_density || app->gpu_volumes[i].has_density;
    }
    app->render_mode = has_density ? VolumeRenderMode::VolumeWithGrid
                                   : VolumeRenderMode::GridOnly;
  }

  std::cout << "Loaded " << path << "\n";
  for (std::size_t i = 0; i < app->scene.notes.size(); ++i) {
    std::cout << "  " << app->scene.notes[i] << "\n";
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
  title += " [" + std::string(RenderModeLabel(app->render_mode)) +
           ", " + ColorModeLabel(app->color_mode) + "]";
  glfwSetWindowTitle(app->window, title.c_str());
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

  if (draw_density) {
    glEnable(GL_BLEND);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
    glDisable(GL_CULL_FACE);
    glDepthMask(GL_FALSE);
    glUseProgram(app->volume_program);
    for (std::size_t i = 0; i < app->gpu_volumes.size(); ++i) {
      const GpuVolume& volume = app->gpu_volumes[i];
      if (!volume.world_bounds.valid || !volume.has_density) continue;
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
      glUniform1f(glGetUniformLocation(app->volume_program, "uValueOffset"),
                  volume.value_offset);
      glUniform1f(glGetUniformLocation(app->volume_program, "uValueScale"),
                  volume.value_scale);
      const float max_extent = std::max(ex.x, std::max(ex.y, ex.z));
      glUniform1f(glGetUniformLocation(app->volume_program, "uDensityGain"),
                  app->density_gain / std::max(max_extent, 1.0e-4f));
      glUniform1i(glGetUniformLocation(app->volume_program, "uFogFromSdf"),
                  app->sdf_fog_mode ? 1 : 0);
      glUniform1f(glGetUniformLocation(app->volume_program, "uSdfBandScale"),
                  volume.sdf_band_scale);
      glUniform1i(glGetUniformLocation(app->volume_program, "uColorMode"),
                  static_cast<int>(app->color_mode));

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
    glDepthMask(GL_TRUE);
    glEnable(GL_CULL_FACE);
    glDisable(GL_BLEND);
  }

  if (draw_grid) {
    glUseProgram(app->line_program);
    SetMat4(app->line_program, "uVP", vp);
    for (std::size_t i = 0; i < app->gpu_volumes.size(); ++i) {
      const LineMesh& lines = app->gpu_volumes[i].grid_lines;
      if (lines.index_count == 0) continue;
      glBindVertexArray(lines.vao);
      glDrawElements(GL_LINES, lines.index_count, GL_UNSIGNED_INT, nullptr);
    }
  }

  glBindVertexArray(0);
}

AppState* GetApp(GLFWwindow* window) {
  return reinterpret_cast<AppState*>(glfwGetWindowUserPointer(window));
}

void FramebufferSizeCallback(GLFWwindow* window, int width, int height) {
  AppState* app = GetApp(window);
  app->framebuffer_width = std::max(width, 1);
  app->framebuffer_height = std::max(height, 1);
}

void CursorPosCallback(GLFWwindow* window, double x, double y) {
  AppState* app = GetApp(window);
  const double dx = x - app->last_cursor_x;
  const double dy = y - app->last_cursor_y;
  app->last_cursor_x = x;
  app->last_cursor_y = y;

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

void MouseButtonCallback(GLFWwindow* window, int button, int action, int) {
  AppState* app = GetApp(window);
  if (button == GLFW_MOUSE_BUTTON_LEFT) app->left_mouse_down = action == GLFW_PRESS;
  if (button == GLFW_MOUSE_BUTTON_MIDDLE) app->middle_mouse_down = action == GLFW_PRESS;
  if (button == GLFW_MOUSE_BUTTON_RIGHT) app->right_mouse_down = action == GLFW_PRESS;
  glfwGetCursorPos(window, &app->last_cursor_x, &app->last_cursor_y);
}

void ScrollCallback(GLFWwindow* window, double, double yoffset) {
  AppState* app = GetApp(window);
  app->camera.distance *= std::pow(0.88f, static_cast<float>(yoffset));
  app->camera.distance = std::max(app->camera.distance, 0.01f);
}

void KeyCallback(GLFWwindow* window, int key, int, int action, int) {
  if (action != GLFW_PRESS) return;
  AppState* app = GetApp(window);
  switch (key) {
    case GLFW_KEY_ESCAPE:
      glfwSetWindowShouldClose(window, GLFW_TRUE);
      break;
    case GLFW_KEY_H:
      PrintControls();
      break;
    case GLFW_KEY_O:
      OpenVdbDialog(app);
      UpdateWindowTitle(app);
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
    default:
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

  app->window = glfwCreateWindow(kWindowWidth, kWindowHeight, "tvdbview", nullptr, nullptr);
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
  if (!app->volume_program || !app->line_program) {
    return false;
  }

  glEnable(GL_DEPTH_TEST);
  glEnable(GL_CULL_FACE);
  glLineWidth(1.0f);
  return true;
}

void Shutdown(AppState* app) {
  ClearGpuVolumes(app);
  if (app->volume_program) glDeleteProgram(app->volume_program);
  if (app->line_program) glDeleteProgram(app->line_program);
#if defined(TVDBVIEW_ENABLE_NFD)
  if (app->nfd_initialized) NFD_Quit();
#endif
  if (app->window) glfwDestroyWindow(app->window);
  glfwTerminate();
}

}  // namespace

int main(int argc, char** argv) {
  AppState app;
  if (!InitGlfwAndGl(&app)) {
    Shutdown(&app);
    return EXIT_FAILURE;
  }

  PrintControls();
  if (argc > 1) {
    LoadSceneIntoApp(&app, argv[1]);
  } else {
    app.camera.resetToBounds(app.scene.bounds);
    std::cout << "No input file. Press O to open a .vdb file.\n";
  }
  UpdateWindowTitle(&app);

  while (!glfwWindowShouldClose(app.window)) {
    glfwPollEvents();
    Draw(&app);
    glfwSwapBuffers(app.window);
  }

  Shutdown(&app);
  return EXIT_SUCCESS;
}
