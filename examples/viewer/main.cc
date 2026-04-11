#include <iostream>
#include <string>

#if TINYVDB_IO_USE_SYSTEM_ZLIB
#include <zlib.h>
#endif

#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"

int main(int argc, char **argv)
{
  if (argc < 2) {
    std::cerr << "Need input.vdb\n";
    return EXIT_FAILURE;
  }

  std::string filename = argv[1];

  std::cout << "Loading : " << filename << "\n";

  return EXIT_SUCCESS;
}
