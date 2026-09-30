# Assert that the hand-maintained SPIR-V fallback include declares exactly the
# array names the shader list maps to.
#
# The fallback is the only SPIR-V source in a build without glslangValidator, and
# it is hand-maintained, so a shader added to the list without adding its symbol
# there produces a build that fails to compile -- and only in that configuration.
# Every array in the fallback is a zero-length {0} placeholder, so nothing else
# would catch a missing entry. This runs in both configurations so the file
# cannot drift.
#
# Invoked as:
#   cmake -DGVK_CMAKE=<path> -DGVK_FALLBACK=<path> -P check_spv_fallback.cmake

if(NOT GVK_CMAKE OR NOT GVK_FALLBACK)
  message(FATAL_ERROR "check_spv_fallback: GVK_CMAKE and GVK_FALLBACK are required")
endif()

file(READ "${GVK_CMAKE}" cml)
file(READ "${GVK_FALLBACK}" fb)

# MATCHALL yields whole matches, so each one is reduced to just the name with a
# second anchored replace. Doing it per match avoids a consume-and-restart loop,
# which silently truncated the list to its first entry.
string(REGEX MATCHALL "set\\(_array [A-Za-z0-9_]+\\)" mapped_full "${cml}")
set(mapped "")
foreach(m IN LISTS mapped_full)
  string(REGEX REPLACE "^set\\(_array ([A-Za-z0-9_]+)\\)$" "\\1" one "${m}")
  list(APPEND mapped "${one}")
endforeach()

string(REGEX MATCHALL "static const uint8_t [A-Za-z0-9_]+\\[\\]" declared_full "${fb}")
set(declared "")
foreach(d IN LISTS declared_full)
  string(REGEX REPLACE "^static const uint8_t ([A-Za-z0-9_]+)\\[\\]$" "\\1" one "${d}")
  list(APPEND declared "${one}")
endforeach()

list(LENGTH mapped n_mapped)
list(LENGTH declared n_declared)
if(n_mapped EQUAL 0)
  message(FATAL_ERROR "check_spv_fallback: no set(_array ...) names found in ${GVK_CMAKE}")
endif()
if(n_mapped LESS 16)
  message(FATAL_ERROR
    "check_spv_fallback: only ${n_mapped} array names parsed from ${GVK_CMAKE}; "
    "the extraction is broken, not the fallback")
endif()

# A mapped name with no fallback symbol breaks any build without the validator.
set(missing "")
foreach(a IN LISTS mapped)
  list(FIND declared "${a}" idx)
  if(idx EQUAL -1)
    list(APPEND missing "${a}")
  endif()
endforeach()

# A fallback symbol with no mapping is dead weight, and would silently not be
# regenerated if the file were ever rebuilt from the shader list.
set(orphan "")
foreach(d IN LISTS declared)
  list(FIND mapped "${d}" idx)
  if(idx EQUAL -1)
    list(APPEND orphan "${d}")
  endif()
endforeach()

if(missing)
  string(REPLACE ";" ", " missing_pretty "${missing}")
  message(FATAL_ERROR
    "check_spv_fallback: ${GVK_FALLBACK} is missing array(s): ${missing_pretty}\n"
    "A build without glslangValidator would fail to compile. Add a zero-length "
    "placeholder 'static const uint8_t <name>[] = {0};' plus its '_len = 0'.")
endif()
if(orphan)
  string(REPLACE ";" ", " orphan_pretty "${orphan}")
  message(FATAL_ERROR
    "check_spv_fallback: ${GVK_FALLBACK} declares unmapped symbol(s): ${orphan_pretty}\n"
    "Either remove them or add the missing set(_array ...) mapping.")
endif()

message(STATUS "check_spv_fallback: ${n_mapped} mapped arrays, ${n_declared} fallback symbols, consistent")
