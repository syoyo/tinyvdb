builddir=`pwd`/build-clang-cl
rm -rf ${builddir}
mkdir ${builddir}

cd ${builddir}
cmake -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_TOOLCHAIN_FILE="cmake/clang-cl-msvc-wsl.cmake" \
  -DHOST_ARCH=x64 \
  -DLLVM_NATIVE_TOOLCHAIN="/mnt/data/local/clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04/" \
  -DMSVC_BASE:FILEPATH="/mnt/data/local/msvc/VC/Tools/MSVC/14.26.28801/" \
  -DWINSDK_BASE="/mnt/data/local/msvc/kits/10/" \
  -DWINSDK_VER="10.0.18362.0" \
  ..

