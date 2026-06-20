file(READ "${INPUT}" TVDB_GPU_SPV_INCLUDE)
string(REGEX REPLACE
       "unsigned char [A-Za-z0-9_]+\\[\\]"
       "static const uint8_t ${ARRAY_NAME}[]"
       TVDB_GPU_SPV_INCLUDE "${TVDB_GPU_SPV_INCLUDE}")
string(REGEX REPLACE
       "unsigned int [A-Za-z0-9_]+_len"
       "static const uint32_t ${ARRAY_NAME}_len"
       TVDB_GPU_SPV_INCLUDE "${TVDB_GPU_SPV_INCLUDE}")
file(WRITE "${OUTPUT}" "${TVDB_GPU_SPV_INCLUDE}")
