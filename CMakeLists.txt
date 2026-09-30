cmake_minimum_required(VERSION 3.5)

project(tinyvdb VERSION 0.9.0 LANGUAGES C CXX)

# options
option(TINYVDB_USE_CCACHE "Use ccache for faster recompile." ON)
option(TINYVDB_BUILD_TESTS "Build tests" OFF)
option(TINYVDB_BUILD_BENCH "Build the CPU performance harness (tests/bench_tinyvdb.c)" OFF)
option(TINYVDB_BUILD_EXAMPLES "Build examples" ON)
option(TINYVDB_USE_SYSTEM_ZLIB "Use system zlib instead of bundled miniz" OFF)
option(TINYVDB_USE_ZSTD "Enable ZSTD compression support in BLOSC frames" ON)
option(TINYVDB_USE_SYSTEM_ZSTD "Use system zstd instead of bundled deps/zstd" OFF)
option(TINYVDB_USE_SYSTEM_BLOSC "Link system libblosc for real BLOSC framing in NanoVDB I/O" OFF)
option(TINYVDB_BUILD_VDBRENDER "Build vdbrender volume path tracer example" ON)
option(TINYVDB_BUILD_TVDBVIEW "Build tvdbview OpenGL VDB viewer example" ON)
option(TINYVDB_BUILD_PYTHON "Build Python extension" OFF)
option(TINYVDB_OPENMP "Enable OpenMP parallelism in mesh/ops kernels" OFF)
option(TINYVDB_SIMD "Enable SSE2/AVX2/F16C SIMD paths (x86-64 only; scalar fallback otherwise)" ON)
option(TINYVDB_BUILD_GPU "Build optional runtime-loaded GPU backend (Vulkan first, CUDA via Driver API + NVRTC)" ON)

# cmake modules
list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/sanitizers)
find_package(Sanitizers QUIET)

# C11 for the library, C++11 for examples
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# [ccache]
if(TINYVDB_USE_CCACHE)
  if(NOT MSVC)
    find_program(CCACHE_EXE ccache)
    if(CCACHE_EXE)
      message(STATUS "Using ccache: ${CCACHE_EXE}")
      set(CMAKE_C_COMPILER_LAUNCHER "${CCACHE_EXE}")
      set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_EXE}")
    endif()
  endif()
endif()

# tinyvdb static library (C11 implementation + miniz + lz4)
set(TINYVDB_C_SOURCES
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_io.c
  ${PROJECT_SOURCE_DIR}/src/lz4.c)
if(NOT TINYVDB_USE_SYSTEM_ZLIB)
  list(APPEND TINYVDB_C_SOURCES ${PROJECT_SOURCE_DIR}/src/miniz.c)
endif()

add_library(tinyvdb STATIC ${TINYVDB_C_SOURCES})

# Mesh/ops C helper library
add_library(tinyvdb_mesh_ops STATIC
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_mesh.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_ops.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_sample.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_tsdf.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_topology.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_ray.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_sparse.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_sparse_tree.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_autograd.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_levelset.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_stats.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_grid_index.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_jagged.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_render.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_lifecycle.c
  ${PROJECT_SOURCE_DIR}/src/tvdb_memory.c)
if(NOT WIN32)
  target_link_libraries(tinyvdb_mesh_ops PUBLIC m)
endif()
# tinyvdb_sparse_tree depends on tinyvdb_io.h types (and tvdb_file_open at runtime)
target_link_libraries(tinyvdb_mesh_ops PUBLIC tinyvdb)
target_include_directories(tinyvdb_mesh_ops PUBLIC ${PROJECT_SOURCE_DIR}/src)

if(TINYVDB_OPENMP)
  find_package(OpenMP)
  if(OpenMP_C_FOUND)
    target_link_libraries(tinyvdb_mesh_ops PUBLIC OpenMP::OpenMP_C)
    target_compile_definitions(tinyvdb_mesh_ops PUBLIC TINYVDB_OPENMP_ENABLED=1)
    message(STATUS "OpenMP enabled for tinyvdb_mesh_ops (${OpenMP_C_FLAGS})")
  else()
    message(WARNING "TINYVDB_OPENMP=ON requested but OpenMP not found; building scalar")
  endif()
endif()

if(TINYVDB_SIMD)
  # x86-64 only; on other architectures the scalar fallback is used.
  if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64|amd64")
    if(MSVC)
      target_compile_options(tinyvdb_mesh_ops PRIVATE /arch:AVX2)
      target_compile_options(tinyvdb           PRIVATE /arch:AVX2)
    else()
      target_compile_options(tinyvdb_mesh_ops PRIVATE -msse4.2 -mavx2 -mf16c -mfma)
      target_compile_options(tinyvdb           PRIVATE -msse4.2 -mavx2 -mf16c -mfma)
    endif()
    target_compile_definitions(tinyvdb_mesh_ops PUBLIC TINYVDB_SIMD=1)
    target_compile_definitions(tinyvdb           PUBLIC TINYVDB_SIMD=1)
    message(STATUS "SIMD (SSE4.2/AVX2/F16C) enabled for tinyvdb + tinyvdb_mesh_ops")
  else()
    message(STATUS "TINYVDB_SIMD=ON but architecture is not x86-64; scalar fallback")
  endif()
endif()
set_target_properties(tinyvdb_mesh_ops PROPERTIES
  C_STANDARD 11
  C_STANDARD_REQUIRED ON
  C_EXTENSIONS OFF)

# NanoVDB support library
add_library(tinyvdb_nanovdb STATIC
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_nanovdb.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_to_nanovdb.c)
target_include_directories(tinyvdb_nanovdb PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_link_libraries(tinyvdb_nanovdb PRIVATE tinyvdb)

# Optional: real BLOSC1 framing (replaces the LZ4-with-fake-header fallback).
# When ON, NanoVDB-Codec=BLOSC files written by libnanovdb load correctly.
if(TINYVDB_USE_SYSTEM_BLOSC)
  find_library(BLOSC_LIBRARY NAMES blosc)
  find_path(BLOSC_INCLUDE_DIR NAMES blosc.h)
  if(BLOSC_LIBRARY AND BLOSC_INCLUDE_DIR)
    target_link_libraries(tinyvdb_nanovdb PUBLIC ${BLOSC_LIBRARY})
    target_include_directories(tinyvdb_nanovdb PUBLIC ${BLOSC_INCLUDE_DIR})
    target_compile_definitions(tinyvdb_nanovdb PUBLIC TVDB_HAVE_BLOSC)
    message(STATUS "Found libblosc: ${BLOSC_LIBRARY} (BLOSC framing enabled)")
  else()
    message(FATAL_ERROR "TINYVDB_USE_SYSTEM_BLOSC=ON but libblosc not found. "
                        "Install libblosc-dev or set TINYVDB_USE_SYSTEM_BLOSC=OFF.")
  endif()
endif()
target_include_directories(tinyvdb PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_compile_definitions(tinyvdb PRIVATE TINYVDB_IO_IMPLEMENTATION MINIZ_NO_STDIO)

# Optional GPU backend. It does not link Vulkan/CUDA SDK libraries and does not
# require SDK headers; drivers are loaded at runtime.
if(TINYVDB_BUILD_GPU)
  find_program(TINYVDB_GLSLANG_VALIDATOR glslangValidator)
  find_program(TINYVDB_XXD_EXECUTABLE xxd)
  if(TINYVDB_GLSLANG_VALIDATOR AND TINYVDB_XXD_EXECUTABLE)
    file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/generated)
    foreach(_shader csg sample sample_image sample_quadratic sparse_conv sparse_conv_map sparse_index_scatter sparse_conv_dense sdf_sphere sdf_box sdf_torus ijk_to_index index_probe points_in_grid neighbor_counts neighbor_counts_probe points_in_grid_probe morph prune coarsen refine volume_render ray_samples voxels_along_ray segments_along_ray tsdf stats levelset_check flood splat splat_quadratic points_to_mask voxelize_mark voxelize_compact hash_insert hash_compact sparse_mark sparse_erode sparse_dilate_scatter sparse_finalize merge_scatter active_coords checksum mesh_to_sdf marching_cubes stencil_scalar_scalar stencil_scalar_d csg_d sample_d mesh_to_sdf_bvh measure measure_d cg cg_d stencil_scalar_vec stencil_vec_scalar stencil_vec_vec mean_curvature_flow fast_sweeping_plane fast_sweeping_plane_d comp advect filter sparse_conv_strided conv_transpose_scatter gaussian_forward gaussian_backward gaussian_sh gaussian_project mcmc_relocation mcmc_noise axpy ssim sparse_conv_batched)
      set(_src ${PROJECT_SOURCE_DIR}/src/tinyvdb_gpu_${_shader}.comp)
      set(_spv ${CMAKE_CURRENT_BINARY_DIR}/generated/tinyvdb_gpu_${_shader}.spv)
      set(_tmp ${CMAKE_CURRENT_BINARY_DIR}/generated/tinyvdb_gpu_${_shader}_spv.tmp)
      set(_inc ${CMAKE_CURRENT_BINARY_DIR}/generated/tinyvdb_gpu_${_shader}_spv.inc)
      if(_shader STREQUAL "csg")
        set(_array kTvdbGpuCsgSpv)
      elseif(_shader STREQUAL "sample")
        set(_array kTvdbGpuSampleSpv)
      elseif(_shader STREQUAL "sample_image")
        set(_array kTvdbGpuSampleImageSpv)
      elseif(_shader STREQUAL "sample_quadratic")
        set(_array kTvdbGpuSampleQuadraticSpv)
      elseif(_shader STREQUAL "sparse_conv")
        set(_array kTvdbGpuSparseConvSpv)
      elseif(_shader STREQUAL "sparse_conv_map")
        set(_array kTvdbGpuSparseConvMapSpv)
      elseif(_shader STREQUAL "sparse_index_scatter")
        set(_array kTvdbGpuSparseIndexScatterSpv)
      elseif(_shader STREQUAL "sparse_conv_dense")
        set(_array kTvdbGpuSparseConvDenseSpv)
      elseif(_shader STREQUAL "sdf_sphere")
        set(_array kTvdbGpuSdfSphereSpv)
      elseif(_shader STREQUAL "sdf_box")
        set(_array kTvdbGpuSdfBoxSpv)
      elseif(_shader STREQUAL "sdf_torus")
        set(_array kTvdbGpuSdfTorusSpv)
      elseif(_shader STREQUAL "ijk_to_index")
        set(_array kTvdbGpuIjkToIndexSpv)
      elseif(_shader STREQUAL "index_probe")
        set(_array kTvdbGpuIndexProbeSpv)
      elseif(_shader STREQUAL "points_in_grid")
        set(_array kTvdbGpuPointsInGridSpv)
      elseif(_shader STREQUAL "points_in_grid_probe")
        set(_array kTvdbGpuPointsInGridProbeSpv)
      elseif(_shader STREQUAL "neighbor_counts")
        set(_array kTvdbGpuNeighborCountsSpv)
      elseif(_shader STREQUAL "neighbor_counts_probe")
        set(_array kTvdbGpuNeighborCountsProbeSpv)
      elseif(_shader STREQUAL "morph")
        set(_array kTvdbGpuMorphSpv)
      elseif(_shader STREQUAL "prune")
        set(_array kTvdbGpuPruneSpv)
      elseif(_shader STREQUAL "coarsen")
        set(_array kTvdbGpuCoarsenSpv)
      elseif(_shader STREQUAL "refine")
        set(_array kTvdbGpuRefineSpv)
      elseif(_shader STREQUAL "volume_render")
        set(_array kTvdbGpuVolumeRenderSpv)
      elseif(_shader STREQUAL "ray_samples")
        set(_array kTvdbGpuRaySamplesSpv)
      elseif(_shader STREQUAL "voxels_along_ray")
        set(_array kTvdbGpuVoxelsAlongRaySpv)
      elseif(_shader STREQUAL "segments_along_ray")
        set(_array kTvdbGpuSegmentsAlongRaySpv)
      elseif(_shader STREQUAL "tsdf")
        set(_array kTvdbGpuTsdfSpv)
      elseif(_shader STREQUAL "stats")
        set(_array kTvdbGpuStatsSpv)
      elseif(_shader STREQUAL "levelset_check")
        set(_array kTvdbGpuLevelsetCheckSpv)
      elseif(_shader STREQUAL "flood")
        set(_array kTvdbGpuFloodSpv)
      elseif(_shader STREQUAL "splat")
        set(_array kTvdbGpuSplatSpv)
      elseif(_shader STREQUAL "splat_quadratic")
        set(_array kTvdbGpuSplatQuadraticSpv)
      elseif(_shader STREQUAL "points_to_mask")
        set(_array kTvdbGpuPointsToMaskSpv)
      elseif(_shader STREQUAL "voxelize_mark")
        set(_array kTvdbGpuVoxelizeMarkSpv)
      elseif(_shader STREQUAL "voxelize_compact")
        set(_array kTvdbGpuVoxelizeCompactSpv)
      elseif(_shader STREQUAL "hash_insert")
        set(_array kTvdbGpuHashInsertSpv)
      elseif(_shader STREQUAL "hash_compact")
        set(_array kTvdbGpuHashCompactSpv)
      elseif(_shader STREQUAL "sparse_mark")
        set(_array kTvdbGpuSparseMarkSpv)
      elseif(_shader STREQUAL "sparse_erode")
        set(_array kTvdbGpuSparseErodeSpv)
      elseif(_shader STREQUAL "sparse_dilate_scatter")
        set(_array kTvdbGpuSparseDilateScatterSpv)
      elseif(_shader STREQUAL "sparse_finalize")
        set(_array kTvdbGpuSparseFinalizeSpv)
      elseif(_shader STREQUAL "merge_scatter")
        set(_array kTvdbGpuMergeScatterSpv)
      elseif(_shader STREQUAL "active_coords")
        set(_array kTvdbGpuActiveCoordsSpv)
      elseif(_shader STREQUAL "checksum")
        set(_array kTvdbGpuChecksumSpv)
      elseif(_shader STREQUAL "stencil_scalar_scalar")
        set(_array kTvdbGpuStencilScalarScalarSpv)
      elseif(_shader STREQUAL "stencil_scalar_d")
        set(_array kTvdbGpuStencilScalarDSpv)
      elseif(_shader STREQUAL "csg_d")
        set(_array kTvdbGpuCsgDSpv)
      elseif(_shader STREQUAL "sample_d")
        set(_array kTvdbGpuSampleDSpv)
      elseif(_shader STREQUAL "mesh_to_sdf_bvh")
        set(_array kTvdbGpuMeshToSdfBvhSpv)
      elseif(_shader STREQUAL "measure")
        set(_array kTvdbGpuMeasureSpv)
      elseif(_shader STREQUAL "fast_sweeping_plane_d")
        set(_array kTvdbGpuFastSweepingPlaneDSpv)
      elseif(_shader STREQUAL "filter")
        set(_array kTvdbGpuFilterSpv)
      elseif(_shader STREQUAL "advect")
        set(_array kTvdbGpuAdvectSpv)
      elseif(_shader STREQUAL "comp")
        set(_array kTvdbGpuCompSpv)
      elseif(_shader STREQUAL "measure_d")
        set(_array kTvdbGpuMeasureDSpv)
      elseif(_shader STREQUAL "cg")
        set(_array kTvdbGpuCgSpv)
      elseif(_shader STREQUAL "cg_d")
        set(_array kTvdbGpuCgDSpv)
      elseif(_shader STREQUAL "stencil_scalar_vec")
        set(_array kTvdbGpuStencilScalarVecSpv)
      elseif(_shader STREQUAL "stencil_vec_scalar")
        set(_array kTvdbGpuStencilVecScalarSpv)
      elseif(_shader STREQUAL "fast_sweeping_plane")
        set(_array kTvdbGpuFastSweepingPlaneSpv)
      elseif(_shader STREQUAL "mean_curvature_flow")
        set(_array kTvdbGpuMeanCurvatureFlowSpv)
      elseif(_shader STREQUAL "stencil_vec_vec")
        set(_array kTvdbGpuStencilVecVecSpv)
      elseif(_shader STREQUAL "mesh_to_sdf")
        set(_array kTvdbGpuMeshToSdfSpv)
      elseif(_shader STREQUAL "marching_cubes")
        set(_array kTvdbGpuMarchingCubesSpv)
      elseif(_shader STREQUAL "sparse_conv_strided")
        set(_array kTvdbGpuSparseConvStridedSpv)
      elseif(_shader STREQUAL "conv_transpose_scatter")
        set(_array kTvdbGpuConvTransposeScatterSpv)
      elseif(_shader STREQUAL "gaussian_forward")
        set(_array kTvdbGpuGaussianForwardSpv)
      elseif(_shader STREQUAL "gaussian_backward")
        set(_array kTvdbGpuGaussianBackwardSpv)
      elseif(_shader STREQUAL "gaussian_sh")
        set(_array kTvdbGpuGaussianShSpv)
      elseif(_shader STREQUAL "gaussian_project")
        set(_array kTvdbGpuGaussianProjectSpv)
      elseif(_shader STREQUAL "mcmc_relocation")
        set(_array kTvdbGpuMcmcRelocationSpv)
      elseif(_shader STREQUAL "mcmc_noise")
        set(_array kTvdbGpuMcmcNoiseSpv)
      elseif(_shader STREQUAL "axpy")
        set(_array kTvdbGpuAxpySpv)
      elseif(_shader STREQUAL "ssim")
        set(_array kTvdbGpuSsimSpv)
      elseif(_shader STREQUAL "sparse_conv_batched")
        set(_array kTvdbGpuSparseConvBatchedSpv)
      else()
        # Falling back to a neighbouring array name silently emits a .inc that
        # redefines another shader's symbol, which shows up much later as a
        # confusing redefinition or missing-symbol error. Fail here instead.
        message(FATAL_ERROR "No SPIR-V array name mapped for shader '${_shader}'. Add an elseif(_shader STREQUAL \"${_shader}\") branch above.")
      endif()
      add_custom_command(
        OUTPUT ${_inc}
        COMMAND ${TINYVDB_GLSLANG_VALIDATOR} -V ${_src} -o ${_spv}
        COMMAND ${TINYVDB_XXD_EXECUTABLE} -i ${_spv} ${_tmp}
        COMMAND ${CMAKE_COMMAND}
                -DINPUT=${_tmp}
                -DOUTPUT=${_inc}
                -DARRAY_NAME=${_array}
                -P ${PROJECT_SOURCE_DIR}/src/tinyvdb_gpu_spv.cmake
        DEPENDS ${_src} ${PROJECT_SOURCE_DIR}/src/tinyvdb_gpu_spv.cmake
        VERBATIM)
      list(APPEND TINYVDB_GPU_SHADER_INCS ${_inc})
    endforeach()
  else()
    set(TINYVDB_GPU_SHADER_INCS ${PROJECT_SOURCE_DIR}/src/tinyvdb_gpu_spv_fallback.inc)
  endif()
  add_custom_target(tinyvdb_gpu_spv DEPENDS ${TINYVDB_GPU_SHADER_INCS})
  add_library(tinyvdb_gpu STATIC ${PROJECT_SOURCE_DIR}/src/tinyvdb_gpu.c ${TINYVDB_GPU_SHADER_INCS})
  add_dependencies(tinyvdb_gpu tinyvdb_gpu_spv)
  set_source_files_properties(${TINYVDB_GPU_SHADER_INCS} PROPERTIES GENERATED TRUE HEADER_FILE_ONLY TRUE)
  target_include_directories(tinyvdb_gpu PUBLIC ${PROJECT_SOURCE_DIR}/src)
  target_include_directories(tinyvdb_gpu PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/generated)
  target_link_libraries(tinyvdb_gpu PUBLIC tinyvdb_mesh_ops tinyvdb_nanovdb)
  if(NOT WIN32)
    target_link_libraries(tinyvdb_gpu PRIVATE ${CMAKE_DL_LIBS})
  endif()
endif()

# When building the Python extension, static libs linked into modules must be PIC
if(TINYVDB_BUILD_PYTHON)
    set_target_properties(tinyvdb PROPERTIES POSITION_INDEPENDENT_CODE ON)
    set_target_properties(tinyvdb_mesh_ops PROPERTIES POSITION_INDEPENDENT_CODE ON)
    set_target_properties(tinyvdb_nanovdb PROPERTIES POSITION_INDEPENDENT_CODE ON)
    if(TINYVDB_BUILD_GPU)
      set_target_properties(tinyvdb_gpu PROPERTIES POSITION_INDEPENDENT_CODE ON)
    endif()
endif()

# Force system zlib for iOS
if(IOS)
  set(TINYVDB_USE_SYSTEM_ZLIB ON CACHE INTERNAL "" FORCE)
endif()

if(TINYVDB_USE_SYSTEM_ZLIB)
  find_package(ZLIB REQUIRED)
  target_link_libraries(tinyvdb PUBLIC ZLIB::ZLIB)
  target_compile_definitions(tinyvdb PUBLIC TVDB_USE_SYSTEM_ZLIB)
endif()

# ZSTD
if(TINYVDB_USE_ZSTD)
  if(TINYVDB_USE_SYSTEM_ZSTD)
    find_package(PkgConfig QUIET)
    if(PkgConfig_FOUND)
      pkg_check_modules(ZSTD IMPORTED_TARGET libzstd)
    endif()
    if(ZSTD_FOUND)
      target_link_libraries(tinyvdb PUBLIC PkgConfig::ZSTD)
    else()
      find_library(ZSTD_LIBRARY NAMES zstd)
      find_path(ZSTD_INCLUDE_DIR NAMES zstd.h)
      if(ZSTD_LIBRARY AND ZSTD_INCLUDE_DIR)
        target_link_libraries(tinyvdb PUBLIC ${ZSTD_LIBRARY})
        target_include_directories(tinyvdb PUBLIC ${ZSTD_INCLUDE_DIR})
      else()
        message(FATAL_ERROR "System zstd not found. Install libzstd-dev or set TINYVDB_USE_SYSTEM_ZSTD=OFF")
      endif()
    endif()
  else()
    # Use bundled single-file zstd from deps/
    target_sources(tinyvdb PRIVATE ${PROJECT_SOURCE_DIR}/deps/zstd.c)
    target_include_directories(tinyvdb PUBLIC ${PROJECT_SOURCE_DIR}/deps)
  endif()
  target_compile_definitions(tinyvdb PUBLIC TVDB_USE_ZSTD)
endif()

# Tests
if(TINYVDB_BUILD_TESTS)
  add_executable(test_ops ${PROJECT_SOURCE_DIR}/tests/test_ops.c)
  target_link_libraries(test_ops PRIVATE tinyvdb_mesh_ops)
  enable_testing()
  add_test(NAME test_ops COMMAND test_ops)

  add_executable(test_hardening ${PROJECT_SOURCE_DIR}/tests/test_hardening.c)
  target_link_libraries(test_hardening PRIVATE tinyvdb_mesh_ops)
  add_test(NAME test_hardening COMMAND test_hardening)

  add_executable(test_alloc_failure ${PROJECT_SOURCE_DIR}/tests/test_alloc_failure.c)
  target_link_libraries(test_alloc_failure PRIVATE tinyvdb_mesh_ops)
  add_test(NAME test_alloc_failure COMMAND test_alloc_failure)

  add_executable(test_sparse_tree ${PROJECT_SOURCE_DIR}/tests/test_sparse_tree.c)
  target_link_libraries(test_sparse_tree PRIVATE tinyvdb_mesh_ops tinyvdb)
  add_test(NAME test_sparse_tree
           COMMAND test_sparse_tree ${PROJECT_SOURCE_DIR}/sphere.vdb)

  add_executable(test_grid_from_sparse ${PROJECT_SOURCE_DIR}/tests/test_grid_from_sparse.c)
  target_link_libraries(test_grid_from_sparse PRIVATE tinyvdb_mesh_ops tinyvdb)
  add_test(NAME test_grid_from_sparse
           COMMAND test_grid_from_sparse ${PROJECT_SOURCE_DIR}/sphere.vdb)

  add_executable(test_simd ${PROJECT_SOURCE_DIR}/tests/test_simd.c)
  target_link_libraries(test_simd PRIVATE tinyvdb_mesh_ops)
  # Inherit the SIMD compile flags from tinyvdb_mesh_ops via PUBLIC define;
  # we also set them locally so the test exercises the same code paths.
  if(TINYVDB_SIMD AND CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64|amd64")
    if(MSVC)
      target_compile_options(test_simd PRIVATE /arch:AVX2)
    else()
      target_compile_options(test_simd PRIVATE -msse4.2 -mavx2 -mf16c -mfma)
    endif()
  endif()
  add_test(NAME test_simd COMMAND test_simd)

  add_executable(test_fast_sweeping ${PROJECT_SOURCE_DIR}/tests/test_fast_sweeping.c)
  target_link_libraries(test_fast_sweeping PRIVATE tinyvdb_mesh_ops)
  add_test(NAME test_fast_sweeping COMMAND test_fast_sweeping)

  add_executable(test_levelset ${PROJECT_SOURCE_DIR}/tests/test_levelset.c)
  target_link_libraries(test_levelset PRIVATE tinyvdb_mesh_ops m)
  add_test(NAME test_levelset COMMAND test_levelset)

  add_executable(test_stats_ops ${PROJECT_SOURCE_DIR}/tests/test_stats_ops.c)
  target_link_libraries(test_stats_ops PRIVATE tinyvdb_mesh_ops m)
  add_test(NAME test_stats_ops COMMAND test_stats_ops)

  add_executable(test_resample_advect ${PROJECT_SOURCE_DIR}/tests/test_resample_advect.c)
  target_link_libraries(test_resample_advect PRIVATE tinyvdb_mesh_ops m)
  add_test(NAME test_resample_advect COMMAND test_resample_advect)

  add_executable(test_grid_index ${PROJECT_SOURCE_DIR}/tests/test_grid_index.c)
  target_link_libraries(test_grid_index PRIVATE tinyvdb_mesh_ops m)
  add_test(NAME test_grid_index COMMAND test_grid_index)

  add_executable(test_jagged ${PROJECT_SOURCE_DIR}/tests/test_jagged.c)
  target_link_libraries(test_jagged PRIVATE tinyvdb_mesh_ops m)
  add_test(NAME test_jagged COMMAND test_jagged)

  add_executable(test_vec3_extend ${PROJECT_SOURCE_DIR}/tests/test_vec3_extend.c)
  target_link_libraries(test_vec3_extend PRIVATE tinyvdb_mesh_ops tinyvdb)
  add_test(NAME test_vec3_extend
           COMMAND test_vec3_extend ${PROJECT_SOURCE_DIR}/sphere.vdb)

  add_executable(test_dense_d ${PROJECT_SOURCE_DIR}/tests/test_dense_d.c)
  target_link_libraries(test_dense_d PRIVATE tinyvdb_mesh_ops m)
  add_test(NAME test_dense_d COMMAND test_dense_d)

  add_executable(test_autograd ${PROJECT_SOURCE_DIR}/tests/test_autograd.c)
  target_link_libraries(test_autograd PRIVATE tinyvdb_mesh_ops m)
  add_test(NAME test_autograd COMMAND test_autograd)

  add_executable(test_nanovdb_transform ${PROJECT_SOURCE_DIR}/tests/test_nanovdb_transform.c)
  target_link_libraries(test_nanovdb_transform PRIVATE tinyvdb_nanovdb m)
  add_test(NAME test_nanovdb_transform COMMAND test_nanovdb_transform)

  add_executable(test_scalar_writer_audit ${PROJECT_SOURCE_DIR}/tests/test_scalar_writer_audit.c)
  target_link_libraries(test_scalar_writer_audit PRIVATE tinyvdb_mesh_ops tinyvdb)
  add_test(NAME test_scalar_writer_audit
           COMMAND test_scalar_writer_audit ${PROJECT_SOURCE_DIR}/sphere.vdb ${CMAKE_BINARY_DIR})

  add_executable(test_corpus_roundtrip ${PROJECT_SOURCE_DIR}/tests/test_corpus_roundtrip.c)
  target_link_libraries(test_corpus_roundtrip PRIVATE tinyvdb m)
  add_test(NAME test_corpus_roundtrip
           COMMAND test_corpus_roundtrip ${PROJECT_SOURCE_DIR} ${CMAKE_BINARY_DIR})

  add_executable(test_reference_roundtrip
                 ${PROJECT_SOURCE_DIR}/tests/test_reference_roundtrip.c)
  target_link_libraries(test_reference_roundtrip PRIVATE tinyvdb m)
  add_test(NAME test_reference_roundtrip
           COMMAND test_reference_roundtrip ${PROJECT_SOURCE_DIR} ${CMAKE_BINARY_DIR})

  add_executable(test_gaussian_backward
                 ${PROJECT_SOURCE_DIR}/tests/test_gaussian_backward.c)
  target_link_libraries(test_gaussian_backward PRIVATE tinyvdb_nanovdb m)
  target_include_directories(test_gaussian_backward PRIVATE
                              ${PROJECT_SOURCE_DIR}/src)
  add_test(NAME test_gaussian_backward COMMAND test_gaussian_backward)

  add_executable(test_nanovdb_reference
                 ${PROJECT_SOURCE_DIR}/tests/test_nanovdb_reference.c)
  target_link_libraries(test_nanovdb_reference PRIVATE
                        tinyvdb_nanovdb tinyvdb m)
  target_include_directories(test_nanovdb_reference PRIVATE
                              ${PROJECT_SOURCE_DIR}/src)
  add_test(NAME test_nanovdb_reference
           COMMAND test_nanovdb_reference ${PROJECT_SOURCE_DIR})

  # Writer/reader agreement. Regression test for the version, name_size and
  # encoded-size mismatches that made every written file unreadable.
  add_executable(test_nanovdb_roundtrip
                 ${PROJECT_SOURCE_DIR}/tests/test_nanovdb_roundtrip.c)
  target_link_libraries(test_nanovdb_roundtrip PRIVATE
                        tinyvdb_nanovdb tinyvdb m)
  target_include_directories(test_nanovdb_roundtrip PRIVATE
                             ${PROJECT_SOURCE_DIR}/src)
  add_test(NAME test_nanovdb_roundtrip
           COMMAND test_nanovdb_roundtrip ${PROJECT_SOURCE_DIR})

  if(TINYVDB_BUILD_GPU)
    add_executable(test_gpu_backend ${PROJECT_SOURCE_DIR}/tests/test_gpu_backend.c)
    target_link_libraries(test_gpu_backend PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    add_test(NAME test_gpu_backend COMMAND test_gpu_backend)
    set_tests_properties(test_gpu_backend PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_gpu_failures ${PROJECT_SOURCE_DIR}/tests/test_gpu_failures.c)
    add_dependencies(test_gpu_failures tinyvdb_gpu_spv)
    target_include_directories(test_gpu_failures PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/generated)
    target_link_libraries(test_gpu_failures PRIVATE tinyvdb_mesh_ops tinyvdb_nanovdb ${CMAKE_DL_LIBS})
    add_test(NAME test_gpu_failures COMMAND test_gpu_failures)

    add_executable(test_gpu_deferred ${PROJECT_SOURCE_DIR}/tests/test_gpu_deferred.c)
    add_dependencies(test_gpu_deferred tinyvdb_gpu_spv)
    target_link_libraries(test_gpu_deferred PRIVATE tinyvdb_gpu)
    if(TINYVDB_GLSLANG_VALIDATOR AND TINYVDB_XXD_EXECUTABLE)
      target_include_directories(test_gpu_deferred PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/generated)
      target_compile_definitions(test_gpu_deferred PRIVATE TVDB_TEST_GENERATED_SPV=1)
    endif()
    add_test(NAME test_gpu_deferred COMMAND test_gpu_deferred)
    set_tests_properties(test_gpu_deferred PROPERTIES SKIP_RETURN_CODE 77)

    # Checks the hand-declared Vulkan ABI in src/tinyvdb_gpu.c against the real
    # <vulkan/vulkan.h>. Skips itself when the SDK headers are not installed,
    # since not requiring them is why the ABI is declared by hand.
    # The SPIR-V fallback include is hand-maintained and is the only shader source
    # when glslangValidator is absent, so a shader mapped but not declared there
    # breaks exactly one build configuration. Checked in both.
    add_test(NAME test_spv_fallback_consistent
             COMMAND ${CMAKE_COMMAND}
                     -DGVK_CMAKE=${PROJECT_SOURCE_DIR}/CMakeLists.txt
                     -DGVK_FALLBACK=${PROJECT_SOURCE_DIR}/src/tinyvdb_gpu_spv_fallback.inc
                     -P ${PROJECT_SOURCE_DIR}/cmake/check_spv_fallback.cmake)

    add_executable(test_gpu_measure ${PROJECT_SOURCE_DIR}/tests/test_gpu_measure.c)
    target_link_libraries(test_gpu_measure PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    target_include_directories(test_gpu_measure PRIVATE ${PROJECT_SOURCE_DIR}/src)
    add_test(NAME test_gpu_measure COMMAND test_gpu_measure)
    set_tests_properties(test_gpu_measure PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_gpu_filter ${PROJECT_SOURCE_DIR}/tests/test_gpu_filter.c)
    target_link_libraries(test_gpu_filter PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    target_include_directories(test_gpu_filter PRIVATE ${PROJECT_SOURCE_DIR}/src)
    add_test(NAME test_gpu_filter COMMAND test_gpu_filter)
    set_tests_properties(test_gpu_filter PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_gpu_advect ${PROJECT_SOURCE_DIR}/tests/test_gpu_advect.c)
    target_link_libraries(test_gpu_advect PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    target_include_directories(test_gpu_advect PRIVATE ${PROJECT_SOURCE_DIR}/src)
    add_test(NAME test_gpu_advect COMMAND test_gpu_advect)
    set_tests_properties(test_gpu_advect PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_gpu_comp ${PROJECT_SOURCE_DIR}/tests/test_gpu_comp.c)
    target_link_libraries(test_gpu_comp PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    target_include_directories(test_gpu_comp PRIVATE ${PROJECT_SOURCE_DIR}/src)
    add_test(NAME test_gpu_comp COMMAND test_gpu_comp)
    set_tests_properties(test_gpu_comp PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_gpu_poisson ${PROJECT_SOURCE_DIR}/tests/test_gpu_poisson.c)
    target_link_libraries(test_gpu_poisson PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    target_include_directories(test_gpu_poisson PRIVATE ${PROJECT_SOURCE_DIR}/src)
    add_test(NAME test_gpu_poisson COMMAND test_gpu_poisson)
    set_tests_properties(test_gpu_poisson PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_vk_abi ${PROJECT_SOURCE_DIR}/tests/test_vk_abi.c)
    add_test(NAME test_vk_abi COMMAND test_vk_abi ${PROJECT_SOURCE_DIR}/src/tinyvdb_gpu.c)

    # Resource-lifetime gate. The parity suite calls each op a handful of times,
    # so it cannot catch descriptor-pool exhaustion or a per-dispatch device
    # object leak; both of those shipped once and were found only by looping.
    add_executable(test_gpu_pde ${PROJECT_SOURCE_DIR}/tests/test_gpu_pde.c)
    target_link_libraries(test_gpu_pde PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    add_test(NAME test_gpu_pde COMMAND test_gpu_pde)
    set_tests_properties(test_gpu_pde PROPERTIES SKIP_RETURN_CODE 77)
    add_test(NAME test_gpu_pde_cuda COMMAND test_gpu_pde c)
    set_tests_properties(test_gpu_pde_cuda PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_gpu_fp64 ${PROJECT_SOURCE_DIR}/tests/test_gpu_fp64.c)
    target_link_libraries(test_gpu_fp64 PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    add_test(NAME test_gpu_fp64 COMMAND test_gpu_fp64)
    set_tests_properties(test_gpu_fp64 PROPERTIES SKIP_RETURN_CODE 77)
    add_test(NAME test_gpu_fp64_cuda COMMAND test_gpu_fp64 c)
    set_tests_properties(test_gpu_fp64_cuda PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_gpu_lifetime ${PROJECT_SOURCE_DIR}/tests/test_gpu_lifetime.c)
    target_link_libraries(test_gpu_lifetime PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    add_test(NAME test_gpu_lifetime COMMAND test_gpu_lifetime 400)
    set_tests_properties(test_gpu_lifetime PROPERTIES SKIP_RETURN_CODE 77)

    # Wavefront-parallel fast sweeping. Every case must match the serial
    # Gauss-Seidel reference within the sqrt tolerance, not merely converge to
    # something plausible: a wrong plane order still produces a smooth field.
    # mesh_to_sdf on meshes with enough faces to matter. The suite's own check is
    # a 4-face tetrahedron with a 10% sign allowance, which cannot distinguish a
    # working kernel from a broken one.
    add_executable(test_gpu_mesh_to_sdf ${PROJECT_SOURCE_DIR}/tests/test_gpu_mesh_to_sdf.c)
    target_link_libraries(test_gpu_mesh_to_sdf PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    add_test(NAME test_gpu_mesh_to_sdf COMMAND test_gpu_mesh_to_sdf)
    set_tests_properties(test_gpu_mesh_to_sdf PROPERTIES SKIP_RETURN_CODE 77)
    add_test(NAME test_gpu_mesh_to_sdf_cuda COMMAND test_gpu_mesh_to_sdf c)
    set_tests_properties(test_gpu_mesh_to_sdf_cuda PROPERTIES SKIP_RETURN_CODE 77)

    # The index-map paths. The 44-case suite's active set is 64 voxels, below
    # TVDB_INDEX_MAP_MIN_ACTIVE, so on both backends it always takes the linear
    # scan and the map is never checked against the CPU. This covers it.
    add_executable(test_gpu_index_map ${PROJECT_SOURCE_DIR}/tests/test_gpu_index_map.c)
    target_link_libraries(test_gpu_index_map PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    add_test(NAME test_gpu_index_map COMMAND test_gpu_index_map)
    set_tests_properties(test_gpu_index_map PROPERTIES SKIP_RETURN_CODE 77)
    add_test(NAME test_gpu_index_map_cuda COMMAND test_gpu_index_map c)
    set_tests_properties(test_gpu_index_map_cuda PROPERTIES SKIP_RETURN_CODE 77)

    add_executable(test_gpu_fast_sweeping ${PROJECT_SOURCE_DIR}/tests/test_gpu_fast_sweeping.c)
    target_link_libraries(test_gpu_fast_sweeping PRIVATE tinyvdb_gpu tinyvdb_mesh_ops tinyvdb_nanovdb m)
    add_test(NAME test_gpu_fast_sweeping COMMAND test_gpu_fast_sweeping)
    set_tests_properties(test_gpu_fast_sweeping PROPERTIES SKIP_RETURN_CODE 77)
    add_test(NAME test_gpu_fast_sweeping_cuda COMMAND test_gpu_fast_sweeping c)
    set_tests_properties(test_gpu_fast_sweeping_cuda PROPERTIES SKIP_RETURN_CODE 77)
  endif()

  if(TINYVDB_BUILD_PYTHON)
    find_program(PYTHON3_EXE NAMES python3 python)
    if(PYTHON3_EXE)
      add_test(NAME test_bridge_ops_py
               COMMAND ${PYTHON3_EXE} ${PROJECT_SOURCE_DIR}/tests/test_bridge_ops.py)
      set_tests_properties(test_bridge_ops_py PROPERTIES
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        ENVIRONMENT "PYTHONPATH=${CMAKE_BINARY_DIR}")
    endif()
  endif()
endif()

# Performance harness. Not a ctest: it is a measurement tool, and a slow
# machine should not fail the suite. Build with -DTINYVDB_BUILD_BENCH=ON.
if(TINYVDB_BUILD_BENCH)
  add_executable(bench_tinyvdb ${PROJECT_SOURCE_DIR}/tests/bench_tinyvdb.c)
  target_link_libraries(bench_tinyvdb PRIVATE
                        tinyvdb_nanovdb tinyvdb_mesh_ops tinyvdb m)
  target_include_directories(bench_tinyvdb PRIVATE ${PROJECT_SOURCE_DIR}/src)
endif()

# Examples
if(TINYVDB_BUILD_EXAMPLES)
  add_subdirectory(examples/vdbdump)
  add_subdirectory(examples/nanovdbdump)
  add_subdirectory(examples/nanovdb_test)
  if(TINYVDB_BUILD_TVDBVIEW)
    add_subdirectory(examples/tvdbview)
  endif()
endif()

# vdbrender (volume path tracer)
if(TINYVDB_BUILD_VDBRENDER)
  add_subdirectory(examples/vdbrender)
endif()

# Python extension
if(TINYVDB_BUILD_PYTHON)
    add_subdirectory(python)
endif()

# [VisualStudio]
if(WIN32)
  set_property(DIRECTORY PROPERTY VS_STARTUP_PROJECT tinyvdb)
endif()
