# TinyVDB viewer

Simple .vdb viewer

## Reuirements

* CMake 3.5 or later
* OpenGL 3.0 or later
* C++11 compiler

## How to build

See `scripts/bootstrap-linux.sh` for example.

```
$ mkdir build
$ cd build
$ cmake -DBLOSC_INCDIR=</path/to/blosc/include> -DBLOSC_LIBRARY=</path/to/libblosc.a> ..
$ make
```

## How to run

```
$ ./tvdb_view <input.vdb>
```
