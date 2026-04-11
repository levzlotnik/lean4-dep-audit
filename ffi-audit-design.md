# FFI Boundary Audit — Design

## Goal

Given an `@[extern "symbol_name"]` constant, classify it into one of three tiers:

| Tier | Condition | Trust level |
|------|-----------|-------------|
| **Standard library** | Symbol found in toolchain `.a`/`.so` | Silent by default — these are Lean's own runtime |
| **Transparent extern** | Symbol has a C source file compiled as part of the package | Flagged — but auditable, source is inspectable |
| **Opaque extern** | Symbol in a `.a`/`.so` that's not toolchain, no source found | Flagged aggressively — black box, uninspectable |

A fourth case, **unresolved**, covers symbols not found anywhere.

## What Lake Metaprogramming Gives Us

The critical constraint: Lake's `Workspace` is only available from `ScriptM` (= `LakeT IO`), which means `lake script run` or `lake exe` context. It is NOT available from `MetaM` or `CommandElabM` — so `#audit` at elaboration time cannot do provenance resolution. This must be a separate `lake exe audit` or `lake script run audit` step.

### Workspace-level (via `ws.lakeEnv`)

From `getWorkspace : ScriptM Workspace`:

```
ws.lakeEnv.lean.sysroot       -- toolchain root (~/.elan/toolchains/...)
ws.lakeEnv.lean.systemLibDir   -- sysroot/lib (libleanrt.a, libleanshared.so)
ws.lakeEnv.lean.leanLibDir     -- sysroot/lib/lean (module .olean/.a files)
ws.lakeEnv.lean.includeDir     -- sysroot/include (lean.h, lean_gmp.h)
```

### Package-level (via `ws.packages`)

For each `pkg : Package`:

```
pkg.dir                        -- root directory of the package
pkg.baseName                   -- package name
pkg.buildDir                   -- .lake/build
pkg.staticLibDir               -- where built .a files end up
pkg.config.moreLinkArgs        -- [-l, -L] flags for system library linking
pkg.targetDecls                -- all declared build targets
```

### Target introspection

`pkg.targetDecls` is `Array (PConfigDecl pkg.keyName)`. Each entry has:

```
decl.name : Name               -- target name (e.g., `libffi`)
decl.kind : Name               -- target kind
```

Filter for extern libraries:
```lean
pkg.targetDecls.filter fun decl => decl.kind == ExternLib.configKind
-- ExternLib.configKind = `extern_lib
```

### What we CANNOT get from the build config

`ExternLibConfig` is:

```lean
structure ExternLibConfig (pkgName name : Name) where
  getPath : Job (CustomData pkgName (name.str "static")) → Job FilePath
```

It's a build function (a `Job` transformer), not a data declaration. The specific `.c` source paths passed to `inputTextFile` inside the `extern_lib` body are embedded in a closure — opaque at runtime.

This means: **we cannot extract C source paths from the Lake build config.** We must discover them by scanning the filesystem.

## Resolution Algorithm

### Step 1: Identify standard library symbols

```
sysroot/lib/          → nm all .a/.so files
sysroot/lib/lean/     → nm module .a files (libInit.a, libLean.a, etc.)
```

If the extern symbol is defined (T symbol in `nm` output) in any of these, classify as **standard library**.

For header-only inlines (e.g., `lean_nat_add` in `lean.h`), the symbol won't appear in any `.a`/`.so`. We can detect these by scanning `sysroot/include/lean/lean.h` for `static inline` functions matching the symbol name. These are also standard library.

### Step 2: Check package build artifacts

For each package with `extern_lib` targets:

```
pkg.staticLibDir/     → nm all .a files
```

If the symbol is defined there, we know which package provides it. But is it transparent?

### Step 3: Search for C source

For the package that provides the symbol, scan `pkg.dir` recursively for `.c`/`.cpp`/`.h` files. Search file contents for patterns like:

```
LEAN_EXPORT ... symbol_name
```

The `LEAN_EXPORT` macro is the standard way to define FFI functions for Lean. Matching `LEAN_EXPORT` + the symbol name in the same declaration is a high-confidence signal.

If found → **transparent extern** (with the source file path).
If not found → **opaque extern** (linked `.a`/`.so` but no inspectable source).

### Step 4: Check moreLinkArgs

For symbols not found in any built `.a`, check `pkg.config.moreLinkArgs` for `-l` flags. These link system libraries (e.g., `-lglfw`, `-lm`). Symbols from system libraries are **opaque extern** — the binary depends on them at link time, but we don't have their source.

### Step 5: Unresolved

If the symbol isn't found in any toolchain library, package artifact, or system library path → **unresolved**. This is a red flag: the `@[extern]` declaration has no backing implementation. The binary will fail to link or crash at runtime.

## Data Types

```lean
inductive ExternProvenance where
  /-- Symbol in toolchain lib (libleanrt.a, libInit.a, etc.) -/
  | standardLib  (lib : FilePath)
  /-- Symbol in toolchain lean.h as static inline -/
  | standardHeader
  /-- Symbol in a package-built .a AND has a matching C source file -/
  | transparentExtern (lib : FilePath) (source : FilePath)
  /-- Symbol in a package-built .a but no source file found -/
  | opaqueExtern (lib : FilePath)
  /-- Symbol referenced in moreLinkArgs system library -/
  | systemLib (flag : String)
  /-- Symbol not found in any searched location -/
  | unresolved
```

## Execution Context

| Context | Provenance available? | Why |
|---------|----------------------|-----|
| `#audit` (elaboration time) | No | `MetaM`/`CommandElabM` don't have `MonadWorkspace` |
| `lake exe audit` | Yes | Runs as compiled native code with access to `ScriptM`/`LakeT IO` |
| `lake script run audit` | Yes | Same — `ScriptFn = List String → ScriptM ExitCode` |

This means provenance resolution is exclusively a CLI feature. The `#audit` command can do everything else (classification, DAG, drill-down) but cannot trace symbols to libraries or source files.

## Implementation Plan

1. Define `ExternProvenance` in `Types.lean`
2. Add `provenance : Option ExternProvenance` field to `FindingInfo` (defaults to `none`)
3. Write `resolveProvenance : AuditResult → ScriptM AuditResult` — the post-processing step that:
   - Gets workspace via `getWorkspace`
   - Builds a map of symbol → library by `nm`-ing all relevant `.a`/`.so` files
   - Scans C source files for `LEAN_EXPORT` + symbol patterns
   - Fills in the `provenance` field for each `extern_` finding
4. Wire it into the `lake exe audit` CLI pipeline (after `auditConst`, alongside `resolveLocations`)
5. Add tests using the existing `FfiFixture` package:
   - `test_ffi_add` should resolve to `transparentExtern` (has `c/ffi.c`)
   - `lean_nat_add` (stdlib) should resolve to `standardLib` or `standardHeader`
   - `test_c_fn` (TestFixtures/Extern.lean — no backing C) should resolve to `unresolved`

## Open Questions

- **Alloy detection**: Alloy generates C code with `_alloy_c_l_` prefix symbols. We could detect this prefix pattern and classify as transparent (since the source is in the `.lean` file itself). Worth doing?
- **Header-only detection accuracy**: Scanning `lean.h` for `static inline` + symbol name might have false positives. Is grep sufficient or do we need a lightweight C parser?
- **Cross-package resolution**: If package A links package B's `.a`, and the symbol is defined in B's source — should we trace back to B's source? The current algorithm handles this naturally (we check all packages).
- **nm availability**: We shell out to `nm`. Should we fall back gracefully if `nm` isn't on PATH? Or just error?

## Verified API Surface (Lean 4.29.0, Lake 5.0.0)

All of the following typecheck:

```lean
import Lake
open Lake

-- From ScriptM:
def example : ScriptM Unit := do
  let ws ← getWorkspace

  -- Toolchain
  let _ := ws.lakeEnv.lean.sysroot
  let _ := ws.lakeEnv.lean.systemLibDir
  let _ := ws.lakeEnv.lean.leanLibDir
  let _ := ws.lakeEnv.lean.includeDir

  -- Packages
  for pkg in ws.packages do
    let _ := pkg.dir
    let _ := pkg.baseName
    let _ := pkg.buildDir
    let _ := pkg.staticLibDir
    let _ := pkg.config.moreLinkArgs

    -- extern_lib targets
    for decl in pkg.targetDecls do
      if decl.kind == ExternLib.configKind then
        let _ := decl.name  -- target name
```
