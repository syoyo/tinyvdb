file(READ "${INPUT}" TVDBVIEW_SPV_INCLUDE)
string(REGEX REPLACE
       "unsigned char [A-Za-z0-9_]+\\[\\]"
       "static const uint8_t kVulkanPathTraceSpv[]"
       TVDBVIEW_SPV_INCLUDE "${TVDBVIEW_SPV_INCLUDE}")
string(REGEX REPLACE
       "unsigned int [A-Za-z0-9_]+_len"
       "static const uint32_t kVulkanPathTraceSpv_len"
       TVDBVIEW_SPV_INCLUDE "${TVDBVIEW_SPV_INCLUDE}")
file(WRITE "${OUTPUT}" "${TVDBVIEW_SPV_INCLUDE}")
