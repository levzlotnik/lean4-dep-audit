import Lake
open Lake DSL System

package FfiFixture

lean_lib FfiFixture where
  precompileModules := true

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "ffi.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

extern_lib libffi pkg := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]
