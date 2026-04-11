/* Compile TinyVDBIO implementation as C. */
/* Ensure POSIX functions (ftruncate, etc.) are declared. */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif
#ifndef TINYVDBIO_IMPLEMENTATION
#define TINYVDBIO_IMPLEMENTATION
#endif
#include "tinyvdbio.h"
