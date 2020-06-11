# LLVMPas : An LLVM to Object Pascal compiler

## Command Line

  lpc [options] filename

  - -c Compile to .obj
  - -S Compile to .s
  - -E Not generate .obj .s
  - -dump Output internal information
  - `-O<n>` Optimization level
  - -emit-llvm Generate LLVM
  - -sys-unit Compile the system unit
  - `-Fi<path>` Add the path of the .inc file
  - `-Fl<path>` Add unit search path
  - `-FU<path>` Set .cu file output path
  - `-FE<path>` Set .exe output path
  - -llvm-target LLVM target
  - `-target <C++/LLVM>`  Generate C++ code or LLVM code (planned)

## Target tool

lpc only converts .pas to LLVM's IR assembly code or C++ code of llvm, which needs
to be compiled again using the corresponding command line tool. If you need to compile
LLVM code, you need to install llvm package (linux) or clang (windows).

You can use the pre-compiled LLVM installation package on Windows, which requires
version 3.5 (greater than 3.5 due to some IL instruction syntax changes, which cannot
be compiled). At the same time, mingw32 is required, because some instructions and
exception handling of LLVM still need the support of the GCC code base, and GCC is
also needed to handle the connection.

Download [LLVM for Windows](http://llvm.org/releases/3.5.0/LLVM-3.5.0-win32.exe) To install.
Download [i686-w64-mingw32-gcc-dw2-4.7.4](https://sourceforge.net/projects/mingw-w64/files/Toolchains%20targetting%20Win32/Personal%20Builds/rubenvb/gcc-4.7-release/i686-w64-mingw32-gcc-dw2-4.7.4-release-win32_rubenvb.7z/download)
Unzip to a directory. Be careful not to download non-dw2.

Modify the lpc.cfg file and replace the path with your own:
```
# command for compile .ll to .bc
-tools-ll2bc"""e:\software\llvm\llvm35\bin\clang.exe"" %%input -O%%opt -c -emit-llvm -o %%output"

# command for compile .ll to .o
-tools-ll2obj"""e:\software\llvm\llvm35\bin\clang.exe"" %%input -O%%opt -c -o %%output"

# command for compile .ll to .asm
-tools-ll2asm"""e:\software\llvm\llvm35\bin\clang.exe"" %%input -O%%opt -c -S -o %%output"

# .bc to .asm
-tools-bc2asm"""e:\software\llvm\llvm35\bin\clang.exe"" %%input -O%%opt -c -o %%output"

# link tool
-tools-link"e:\software\mingw32\mingw32-dw2-4.7\bin\g++ -static-libgcc -static-libstdc++"

```
Note the above variables %%input, %%opt, %%output

## Generate system unit

The system unit includes system.pas and ex.ll, and ex.ll contains some code that cannot
be completed by pascal syntax.

```
lpc -sys-unit -c system.pas -FU..\lib\i386-win32\rtl\
clang ex.ll -o ex.o
```

## Unfinished:

  - RTTI Type generation
  - string, variant, interface, dynarray automatic transformation
  - set related code
  - open array
  - ...and many more...
