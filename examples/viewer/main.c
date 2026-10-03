#include <stdio.h>
#include <stdlib.h>

#if TINYVDB_IO_USE_SYSTEM_ZLIB
#include <zlib.h>
#endif

#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"

int main(int argc, char **argv)
{
  if (argc < 2) {
    fprintf(stderr, "Need input.vdb\n");
    return EXIT_FAILURE;
  }

  const char *filename = argv[1];

  printf("Loading : %s\n", filename);

  return EXIT_SUCCESS;
}
