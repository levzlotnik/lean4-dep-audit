# Extern Symbol Provenance in Lean 4: Findings and Open Questions

## Context

We are building an auditor ([lean4-dep-audit](https://github.com/TODO)) that traces `@[extern]` symbols back to their native implementations. Given a Lean constant with `@[extern "symbol_name"]`, the auditor answers: **where does this symbol's implementation live, and can I see the source?**

This involves walking Lake's build trace files (`.trace` JSON) backward from linked artifacts to C source. During implementation, we ran into several questions about how Lake handles native code linking and what the resulting artifact chain looks like.

## What we found

### The Lake trace file chain (for `extern_lib`)

When a package uses the standard `extern_lib` pattern (C source compiled by Lake), the chain is fully traceable:

```
c/ffi.c  -->  cc -c  -->  build/c/ffi.o  -->  ar rcs  -->  build/lib/libffi.a
                           [ffi.o.trace]                    [libffi.a.trace]
```

Each `.trace` file records its inputs with content hashes. The `.a.trace` references its `.o` inputs; each `.o.trace` references its `.c` source. Hashes chain together: the output hash of one step appears as an input hash of the next. This is a content-addressable DAG that we can walk backward from any artifact to its source.

### Three linking mechanisms produce different artifact trails

| Mechanism | Trace chain to source? | Symbol discoverable via `nm`? | Works with `precompileModules`? |
|---|---|---|---|
| `extern_lib` + `buildStaticLib` | Full: `.a.trace` -> `.o.trace` -> `.c` | Yes (`.a` in `build/lib/`) | Yes |
| `input_file` + `moreLinkObjs` | None: no `.a.trace` exists | Only if `.a` is referenced in a link trace | Partially (see below) |
| `moreLinkArgs` (e.g., `-lfoo`) | None: raw flags, no file to inspect | No (would need to resolve `-l` flags to paths) | Depends on system |

### `moreLinkObjs` and `precompileModules` don't fully compose

With `precompileModules := true`, Lake builds per-module shared libraries (`Module.so`) that get `dlopen`'d by the interpreter at elaboration time. When a module declares `@[extern "sym"]`, the interpreter needs `sym` to be available in the loaded `.so`.

`moreLinkObjs` feeds into library-level and executable-level link steps, but **not** into per-module dynlib compilation. The per-module `.so.trace` `linkObjs` array contains only the module's own `.c.o.export` -- not the `moreLinkObjs` targets.

Consequence: `@[extern]` symbols backed by `moreLinkObjs` fail at elaboration time with `undefined symbol` when `precompileModules := true`. This is the same class of issue as [lean4#8448](https://github.com/leanprover/lean4/issues/8448).

`extern_lib` does not have this problem -- its `.a` is linked into all dynlib build steps.

### Lean FFI always requires a C wrapper at the boundary

Lean's FFI calling convention requires functions to accept and return `lean_object*`, use `lean_box`/`lean_unbox`, and participate in reference counting. A vendor shipping a proprietary native library cannot expose their internal API directly as `@[extern]` symbols. The practical pattern is:

```
[Vendor's proprietary .a/.so]  <--  [Thin C wrapper .c]  <--  [@[extern] in .lean]
   (internal API)                    (lean_object* bridge)     (opaque declaration)
```

The wrapper `.c` is always present and always compiled by Lake via `extern_lib`/`buildO`, producing full trace files. The vendor's inner library is linked via `moreLinkArgs` or as an additional link dependency, but its symbols never appear as `@[extern]` names.

This means: **for any `@[extern]` symbol that is actually callable, there is essentially always a `.c` file at the Lean FFI boundary.** The scenario where a Lean-FFI-compatible `.a` exists with no associated source is an edge case that's difficult to construct without fighting Lake's build system.

## Open questions for the Lake team

1. **Is the `moreLinkObjs` / `precompileModules` interaction intentional?** If a `lean_lib` has `moreLinkObjs` pointing to native objects and `precompileModules := true`, the per-module dynlibs are built without those objects, causing `dlopen` failures. Is this a known limitation, a bug, or working as designed? (Related: [lean4#8448](https://github.com/leanprover/lean4/issues/8448))

2. **Is there a supported pattern for distributing pre-built native libraries without C source?** For example, a vendor who wants to ship `@[extern]` bindings backed by a binary-only `.a`. The patterns we tried (`input_file` + `moreLinkObjs`, `extern_lib` + `inputBinFile`) all have caveats. Is there a recommended approach, or is the expectation that the C source is always present in the package?

3. **Are build trace files considered a stable interface?** We parse `.trace` JSON files to extract input/output chains. The schema (`schemaVersion: "2025-09-10"`) includes `inputs`, `outputs`, `log`, and `depHash`. Can downstream tools rely on this structure, or is it an internal implementation detail?

4. **Is `extern_lib` actually deprecated?** The Lake README says "NOTE: `extern_lib` targets are deprecated. Use a custom `target` in conjunction with `moreLinkObjs` / `moreLinkLibs` instead." But `moreLinkObjs` doesn't compose with `precompileModules`, while `extern_lib` does. Is the deprecation premature, or are we missing the intended replacement pattern?

## Provenance classification

For reference, our auditor classifies each `@[extern]` symbol into one of:

| Classification | Meaning | How detected |
|---|---|---|
| `tracedToSource` | Full chain: `.a` -> `.o` -> `.c` exists on disk | Walk `.a.trace` -> `.o.trace` -> check `.c` exists |
| `toolchainRuntime` | Symbol in `libleanrt.a` (Lean runtime) | `nm` + path is under toolchain sysroot |
| `toolchainHeader` | `static inline` in `lean/lean.h` | Scan header file for symbol name |
| `binaryOnly` | Found in a `.a` but no trace chain to source | `nm` finds it, but no `.a.trace` or broken chain |
| `unresolved` | Not found in any scanned library | Not in any `.a` in search paths, not in `lean.h` |

The `binaryOnly` classification is the one that motivated this investigation: it would fire for pre-built `.a` files that Lake didn't compile. As noted above, this appears to be a rare edge case in practice.
