Compiling Prover9, Mace4, and related programs.

Requirements:

  - C compiler: GCC or Clang (C89/C90 compatible).
  - GNU make.
  - On macOS: Xcode command-line tools (provides clang, libtool, make).

Tested with GCC 3.3 through 14.x and Apple Clang 15.x/16.x on
macOS (arm64, x86_64) and Linux (x86_64).


Building
--------

    make all                Build all programs (release, -O2).
    make all DEBUG=1        Build with debug symbols (-g -O0 -DDEBUG).

This compiles:

    ladr library            (ladr/)
    mace4 library           (mace4.src/)
    mace4                   (mace4.src/)
    prover9                 (provers.src/)
    miscellaneous apps      (apps.src/ -- clausefilter, prooftrans, etc.)

then moves all programs and utilities to ./bin/.

On macOS, universal binaries (arm64 + x86_64) are built automatically.
The Makefile uses libtool instead of ar for static libraries. Binaries
are ad-hoc code signed (codesign -s -) to prevent SIGKILL on unsigned
executables.


Cleaning
--------

    make clean              Remove object files and libraries.
    make realclean          Remove objects, libraries, and binaries.


Testing
-------

    make test1              Basic Prover9 tests.
    make test2              Basic Mace4 tests.
    make test3              Utility program tests (prooftrans, etc.).
    make test4              TPTP input/output tests.
    make test5              SinE premise selection tests.

Tests print PASS/FAIL for each case. All tests should pass before
using the binaries.


Notes
-----

1. C89 required. All source code is C89/C90 compatible. Do not use
   C99 features (for-loop initial declarations, mid-block variable
   declarations, // comments). Some build environments use older
   compilers that reject C99.

2. Rebuilding while running. Building overwrites bin/prover9, etc.
   If a long Prover9 or Mace4 run is in progress, the running process
   may be affected. Copy the binary elsewhere before rebuilding, or
   wait for the run to finish.

3. Debug builds. DEBUG=1 enables -g -O0 -DDEBUG. Debug builds include
   memory tracking (safe_malloc/safe_free headers and counters) and
   additional assertions. Release builds omit all tracking overhead.

4. Debian packaging. Earlier releases included a libtoolize.patch
   (contributed by Peter Collingbourne) for building a shared LADR
   library. That patch was for the 2009 Makefiles and has been
   removed. Packagers should adapt the current Makefiles directly.
