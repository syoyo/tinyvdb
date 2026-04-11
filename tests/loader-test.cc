#if defined(TINYVDB_IO_USE_SYSTEM_ZLIB)
// or inclur your own zlib header here.
#include <zlib.h>
#endif

#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <fstream>
//#include <cstdint>


int main(int argc, char **argv)
{
  if (argc < 2) {
    std::cerr << "Need input.vdb" << std::endl;
    return EXIT_FAILURE;
  }

  // 1. Parse VDB header
  tinyvdb::VDBHeader header;
  std::string warn;
  std::string err;
  tinyvdb::VDBStatus status = tinyvdb::ParseVDBHeader(argv[1], &header, &err);

  if (status != tinyvdb::TINYVDBIO_SUCCESS) {
    if (!err.empty()) {
      std::cerr << "error: " << err << std::endl;
    }
    std::cerr << "Failed to parse VDB header. status = " << status << "\n";
    return EXIT_FAILURE;
  }

  // 2. Read Grid descriptors
  std::map<std::string, tinyvdb::GridDescriptor> gd_map;

  status = tinyvdb::ReadGridDescriptors(argv[1], header, &gd_map, &err);
  if (status != tinyvdb::TINYVDBIO_SUCCESS) {
    if (!err.empty()) {
      std::cerr << "error: " << err << std::endl;
    }
    std::cerr << "Failed to read grid descriptors. status = " << status << "\n";
    return EXIT_FAILURE;
  }

  std::cout << "# of grid descriptors = " << gd_map.size() << std::endl;

  // 3. Read Grids
  status = tinyvdb::ReadGrids(argv[1], header, gd_map, &warn, &err);
  if (!warn.empty()) {
    std::cout << "warning: " << warn << std::endl;
  }
  if (status != tinyvdb::TINYVDBIO_SUCCESS) {
    if (!err.empty()) {
      std::cerr << "error: " << err << std::endl;
    }
    std::cerr << "Failed to read grids. status = " << tinyvdb::GetStatusString(status) << "\n";
    return EXIT_FAILURE;
  }


  std::cout << "Load OK" << std::endl;

  return EXIT_SUCCESS;
}
