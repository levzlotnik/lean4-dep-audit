# lean4-dep-audit — Plan

## Goal

Build a Lean 4 metaprogram that traverses any `Expr` (including `IO` terms like `main`) and produces a structured audit report of its transitive dependencies — focusing on axioms, opaques, and `@[extern]` FFI bindings.

## Why

Lean's `#print axioms` only reports axioms and only at the command level. We want:

- Full classification: axioms, opaques, externs, inductives, etc.
- Pointed at arbitrary terms, including IO actions
- Configurable trust boundaries (ignore Init/Std/Lean by default, audit everything if asked)
- Runtime vs kernel-time dependency classification
- For externs: trace the symbol name back to the actual native library/C source

---

## What's Done

### Infrastructure

- **Lake project initialized** with Lean 4.29.0 (`lakefile.toml`, `lean-toolchain`)
- **Nix flake** for dev shell (`flake.nix`) with elan
- **home-manager** set up at `~/.config/home-manager/` with elan, git, rg, uv, cargo, python3.14, cmake, clang, swi-prolog, direnv+nix-direnv
- **direnv** configured (`.envrc` with `use flake`) so project shell activates on `cd`
- **lean-lsp-mcp** configured as local MCP server in `opencode.json` — gives sub-second LSP feedback (goals, diagnostics, hover, search)
- **lean4-skills** installed at `.opencode/skills/lean4/` — workflow/proving skill pack

### Two-Pass Auditor (working)

The auditor uses a two-pass design: a fast pure first pass for classification + DAG construction, and an instant pure second pass for interactive drill-down queries.

#### Pass 1: Classification + DAG (`auditConst`)

**Signature:** `Environment → AuditConfig → Name → AuditResult → AuditResult` (pure, no MetaM)

Walks every `Expr` reachable from the root constant, following `.const` references into the `Environment`. Each constant body is traversed exactly once (guarded by `visited : NameHashSet`). Accepts a `prior : AuditResult` accumulator for incremental/bulk audits. At each constant:

1. Classify via `classifyConst` (axiom/opaque with sub-kind/extern or uninteresting)
2. If it's a finding and `shouldReport`: upsert `FindingInfo` with reachability flags
3. If first encounter: add to `visited`, compute reverse dep edges via `Expr.foldConsts`
4. If `shouldRecurse`: recurse into `ci.type` and `ci.value?`

No paths stored. No `MetaM`. The `ExprPath` is not threaded through the first pass at all — the `ConstContext` carries only `depth : Nat` and `constStack : Array Name` for filter predicates.

**Output:** `AuditResult` containing:
- `findings : NameMap FindingInfo` — interesting constants with classification, reachability flags (`reachableAtRuntime`, `reachableInProof`), source location, and encounter count
- `visited : NameHashSet` — all traversed constants
- `reverseDeps : NameMap NameHashSet` — the constant-level dependency DAG (child → {parents})

**Source locations** are filled in by a separate `resolveLocations : AuditResult → MetaM AuditResult` step that calls `findDeclarationRanges?` for each finding. This is the only part that needs `MetaM` (really just `MonadEnv + MonadLiftT BaseIO`).

#### Pass 2: Interactive Drill-Down (`drillDown`)

**Signature:** `Environment → Name → Name → AuditResult → DrillResult` (pure)

Answers the question: "which direct dependencies of `from_` transitively reach `target`?"

Algorithm:
1. `findAncestors(target)` — BFS upward from target through `reverseDeps` to get the set of all constants that transitively reference it
2. `immediateDeps(from_)` — `Expr.foldConsts` over `from_`'s type + value to get its direct constant references
3. Intersect: which of `from_`'s direct deps are in the ancestor set?

This is O(ancestors + children) per query — effectively instant.

#### Opaque Sub-Classification

Opaque constants are sub-classified via `OpaqueKind`:
- `partial_` — `partial def`, has a Lean body but no termination proof
- `initialize_` — `initialize`/`builtin_initialize` ref, value computed at module init
- `implementedBy_` — body is `@default T inst`, typically a `NonemptyType` implementation
- `other` — catch-all for unclassified opaques

Detection uses `Lean.hasInitAttr`, `Lean.isIOUnitInitFn`, `Lean.isIOUnitBuiltinInitFn`, and `OpaqueVal.value.isAppOfArity ``default 2`.

#### `#audit` Command

Two syntax forms, shared elaborator:

```lean
#audit myMain                                        -- single constant, standard config
#audit myMain with AuditConfig.runtimeExterns         -- single constant, custom config
#audit (myMain, myOther)                              -- multiple constants (shared AuditResult)
#audit (myMain, myOther) with { drill := [`propext] } -- multi + drill
#audit myMain with { shouldReport := Filter.externsOnly }  -- inline custom config
```

The `with` clause accepts any expression of type `AuditConfig`, including user-defined configs. Uses `atomic` + `colGt` for clean parsing without ambiguity.

**Standard config** (`AuditConfig.standard`) — the default when no `with` is given:
- **Skips stdlib recursion**: does not traverse into constants from `Init`, `Lean`, `Std`, or `Mathlib` modules (checked by module name, not constant name)
- **Reports non-standard axioms**: any `axiom` beyond `propext`, `Quot.sound`, `Classical.choice` — these indicate dismissed proof obligations
- **Reports non-standard runtime externs**: `@[extern]` constants from user code (not stdlib)
- **Skips proof-term descent**: no Omega/decidability machinery noise

For a project using only stdlib, the standard config correctly reports 0 findings.

#### `AuditM` Monad

`AuditM := StateT AuditResult MetaM` — thin wrapper for the outer orchestration layer. The pure core functions (`auditConst`, `drillDown`) don't need it. `AuditM` is for sequencing multiple audits, resolving locations, and running drill queries through a shared state.

#### Data Types

**`Types.lean`:**
- `OpaqueKind` — inductive: `partial_`, `initialize_`, `implementedBy_`, `other`
- `Finding` — inductive: `axiom_`, `opaque_ (kind : OpaqueKind)`, `extern_ (sym : String)`
- `ExprStep` — inductive: 13 variants for path tracking (future use)
- `ExprPath` — abbreviation for `Array ExprStep`
- `SourceLocation` — struct: `module : Name`, `range? : Option DeclarationRange`
- `SymbolProvenance` — inductive: `tracedToSource (cFile oFile aFile)`, `toolchainRuntime (lib)`, `toolchainHeader`, `unresolved`
- `FindingInfo` — struct: `name`, `finding`, `type`, `typeStr`, `location`, `reachableAtRuntime`, `reachableInProof`, `numEncounters`, `provenance?`
- `AuditResult` — struct: `findings`, `visited`, `reverseDeps`
- `DrillResult` — struct: `from_`, `target`, `children : List Name`
- `ConstContext` — lightweight predicate context: `env`, `name`, `ci`, `levels`, `finding`, `inProofTerm`, `depth`, `constStack`
- `DescendContext` — structural predicate context: `step`, `currentConst?`, `inProofTerm`
- `AuditConfig` — struct: `shouldRecurse`, `shouldReport`, `shouldDescend` (predicates) + `drill : List Name`

**`Classify.lean`:**
- `getExternSymbol?` — extracts extern symbol from `ExternAttrData.entries`
- `classifyOpaqueKind` — sub-classifies opaques using init attrs and value shape
- `classifyConst` — classifies `ConstantInfo` as interesting or not (externs take priority over opaques)

**`ExternSourceProvenance.lean`:**
- `nmDefinedSymbols` — shells out to `nm --defined-only`, parses output into `Std.HashSet String`
- `parseTraceInputPaths` / `traceStaticLibInputs` / `traceObjectInput` — reads Lake `.trace` JSON files, extracts input file paths
- `isStaticInlineInHeader` — scans `lean.h` for `static inline` declarations matching a symbol
- `indexLibrarySymbols` — builds symbol → `.a` path map from all libs in a directory
- `traceSymbolToSource` — follows full chain: `.a.trace` → `.o` → `nm` → `.o.trace` → `.c` → exists on disk
- `resolveProvenance` — main entry point: processes all extern findings, falls back through toolchain runtime / lean.h header / unresolved

**`Traverse.lean`:**
- `TraversalState` — threads `currentConst?`, `inProofTerm`, `depth`, `constStack`
- `recordDepsFor` — computes reverse dep edges for a constant via `Expr.foldConsts`
- `auditExpr` — partial recursive `Expr` walker (pure, no paths)
- `auditConst` — entry point for pass 1, accepts `prior : AuditResult` accumulator
- `resolveLocations` — fills in source locations (MetaM)
- `findAncestors` — BFS on reverse dep graph
- `immediateDeps` — `foldConsts` for a single constant
- `drillDown` — entry point for pass 2

**`Monad.lean`:**
- `AuditM` — `StateT AuditResult MetaM`
- `auditConstM`, `auditConstsM` — monadic wrappers with shared state
- `resolveLocationsM`, `drillDownM` — monadic wrappers
- `AuditM.run'`, `AuditM.exec` — runners

**`Command.lean`:**
- Syntax: `#audit ident ("with" term)?` and `#audit "(" ident,+ ")" ("with" term)?`
- `extractNames`, `extractConfigStx`, `evalConfig` — syntax parsing
- `formatFinding`, `formatSection`, `formatAuditSummary`, `formatDrill` — output formatting
- `runAudit` — shared elaborator: parses syntax, evaluates config, runs pipeline, displays results

**`StackTrace.lean`:**
- `StackFrame`, `ExprPath.toFrames`, `toStackTrace`, `toCompactTrace` — compile-time stack trace rendering (for future use in detailed path pass)
- `DrillResult.toTraceString` — pretty-print drill results

**`Filter.lean`:**
- `Filter.byName`, `inNamespaces`, `notInNamespaces` — name-based filtering
- `Filter.axiomsOnly`, `opaquesOnly`, `partialsOnly`, `initializeOnly`, `externsOnly` — finding-type filters
- `Filter.runtimeOnly`, `kernelOnly` — runtime vs kernel-time classification
- `Filter.isStandardAxiom`, `isStandardLibrary`, `nonStandardAxiomsOnly`, `nonStandardExternsOnly` — standard library filtering (module-based)
- `Filter.maxDepth`, `pathThrough`, `hasAnyFinding` — structural filters
- `Filter.and`, `or`, `not` — boolean combinators
- `Descend.skipProofTerms`, `skipTypes`, `all` — descent predicates
- `Descend.and`, `or` — boolean combinators
- `AuditConfig.default`, `standard`, `trustPrefixes`, `runtimeOnly`, `runtimeExterns`, `axiomsOnly` — convenience configs

#### Demo Results (`Main.lean`)

Five demos on `myMain : IO Unit` (reads stdin, prints greeting):

1. **Standard audit:** 25 constants visited, 0 findings (correct — pure stdlib user code)
2. **Runtime externs:** 703 constants visited, 58 externs (all stdlib — filtered out by standard config)
3. **Full audit (AuditConfig.default):** 4300 constants visited, 91 findings (3 axioms, 3 opaques, 85 externs)
4. **Drill-down:** "Why does myMain depend on propext?" → IO.println, String.Slice.instToString, instAppendString, String.trimAscii
5. **Multiple constants:** `(myMain, main)` — shared AuditResult, 25 visited, 0 findings

### Test Suite (38 tests, all passing)

Fixtures in `TestFixtures/` (separate `lean_lib`, compiled independently), tests in `Tests/` that import fixtures + auditor. `lake build Tests` = run all tests. Assertion failure = build error.

**Fixture files (in-project):**
- `TestFixtures/Extern.lean` — `@[extern "test_c_fn"]` binding, caller, dual-extern caller
- `TestFixtures/Axiom.lean` — custom `axiom`, `sorry`-based theorem, transitive sorry usage
- `TestFixtures/Opaque.lean` — `partial def`, plain `opaque`, callers for each
- `TestFixtures/PureStdlib.lean` — pure arithmetic, pure IO, list processing (all stdlib-only)
- `TestFixtures/Chain.lean` — known dependency chain with extern leaf for drill-down queries

**Package-level fixture (`test-packages/ffi-fixture/`):**
- A real Lake package with C source compiled via `extern_lib`. The root project depends on it via `require FfiFixture from "test-packages" / "ffi-fixture"`.
- `c/ffi.c` — C implementations: `test_ffi_add` (UInt32 addition), `test_ffi_toggle` (Bool negation), `test_ffi_const42` (thunk returning 42)
- `FfiFixture/Basic.lean` — `@[extern]` opaque declarations matching the C symbols, plus pure Lean callers (`callsFfiAdd`, `callsBothFfi`, `ffiChainRoot`)
- `lakefile.lean` — `extern_lib` target compiling `c/ffi.c` → `libffi.a`, with `precompileModules := true`
- Build produces `libffi.a` with verified symbols (`nm` confirms `test_ffi_add`, `test_ffi_toggle`, `test_ffi_const42`)

**Test files (38 `run_cmd` blocks):**
- `Tests/TestExtern.lean` (4 tests) — extern classification, transitive detection, dual externs, standard config, reachability flags
- `Tests/TestAxiom.lean` (4 tests) — axiom classification, transitive detection, standard config, sorry → `sorryAx` (classified as `extern_ "lean_sorry"` since `@[extern]` takes priority)
- `Tests/TestOpaque.lean` (3 tests) — partial def, implementedBy classification, standard config
- `Tests/TestPureStdlib.lean` (4 tests) — 0 findings for pure code under standard config, >0 findings under default config (validates filtering isn't trivially empty)
- `Tests/TestDrillDown.lean` (4 tests) — single-path drill, multi-path drill, non-existent target, extern finding detection
- `Tests/TestMulti.lean` (3 tests) — shared visited dedup, disjoint trees, combined visit count ≥ individual
- `Tests/TestFfi.lean` (7 tests) — **real linked FFI**: extern classification with correct symbol names, transitive detection through callers, multi-extern detection, drill-down through FFI dependency chains, standard config flags non-standard FFI externs, runtime reachability, thunk-pattern extern
- `Tests/TestTypeInfo.lean` (5 tests) — declared type recording: type field non-default, typeStr populated by resolveLocations, extern/axiom/opaque type strings contain expected fragments
- `Tests/TestProvenance.lean` (4 tests) — **symbol provenance resolution**: `tracedToSource` for FFI fixture (verifies `cFile` contains `ffi.c`), `toolchainRuntime` for stdlib externs in `libleanrt.a`, `toolchainHeader` for `static inline` in `lean.h`, `unresolved` for unlinked test fixture externs

**Test infrastructure:**
- `Tests/Helpers.lean` — assertion helpers (`assertHasFinding`, `assertFindingIs`, `assertReachability`, `assertDrillContains`, `assertTracedToSource`, `assertToolchainRuntime`, `assertToolchainHeader`, `assertUnresolved`, etc.), `runAudit`/`runAuditMulti`/`runAuditWithProvenance` wrappers, `runTest` lifts `MetaM` into `CommandElabM`

**Key finding:** `sorryAx` is classified as `extern_ "lean_sorry"` (not `axiom_`) because `sorryAx` has `@[extern "lean_sorry"]` in the Lean runtime, and the auditor's classification correctly gives extern priority over axiom.

### Project Structure

```
Lean4DepAudit/
  lakefile.lean               # Lake build config (converted from TOML for extern_lib support)
  lean-toolchain              # leanprover/lean4:v4.29.0
  flake.nix                   # nix dev shell with elan
  .envrc                      # direnv: `use flake`
  opencode.json               # lean-lsp-mcp config
  .opencode/skills/lean4/     # lean4-skills pack
  plan.md                     # this file
  Lean4DepAudit.lean      # root import (re-exports all modules)
  Lean4DepAudit/
    Basic.lean                # placeholder (from lake init)
    Types.lean                # OpaqueKind, Finding, FindingInfo, AuditResult, DrillResult, AuditConfig
    Classify.lean             # getExternSymbol?, classifyOpaqueKind, classifyConst
    Traverse.lean             # auditConst (pass 1), drillDown (pass 2), resolveLocations
    Monad.lean                # AuditM, monadic wrappers
    Command.lean              # #audit command elaborator
    StackTrace.lean           # StackFrame, toFrames, toStackTrace, DrillResult.toTraceString
    Filter.lean               # Filter/Descend combinators, standard library detection, convenience configs
    ExternSourceProvenance.lean # IO-based extern symbol → C source tracing via Lake trace files
    CLI.lean                  # CLI: filter DSL parser, arg parser, formatters, run entry point
  test-packages/
    ffi-fixture/              # Real Lake package with C FFI (required dependency)
      lakefile.lean           # extern_lib target, compiles c/ffi.c → libffi.a
      lean-toolchain          # same version as root
      FfiFixture.lean         # root import
      FfiFixture/
        Basic.lean            # @[extern] bindings (ffiAdd, ffiToggle, ffiConst42) + callers
      c/
        ffi.c                 # C implementations (test_ffi_add, test_ffi_toggle, test_ffi_const42)
  TestFixtures.lean           # root import for in-project test fixtures
  TestFixtures/
    Extern.lean               # @[extern] bindings (no backing C — unlinked opaques)
    Axiom.lean                # custom axiom, sorry
    Opaque.lean               # partial def, plain opaque
    PureStdlib.lean           # stdlib-only code
    Chain.lean                # known dependency chain for drill-down
  Tests.lean                  # root import for tests
  Tests/
    Helpers.lean              # assertion helpers, runTest, runAudit wrappers
    TestExtern.lean           # extern tests (4)
    TestAxiom.lean            # axiom tests (4)
    TestOpaque.lean           # opaque tests (3)
    TestPureStdlib.lean       # pure stdlib tests (4)
    TestDrillDown.lean        # drill-down tests (4)
    TestMulti.lean            # multi-constant tests (3)
    TestFfi.lean              # FFI tests (7) — real linked native code
    TestProvenance.lean       # provenance tests (4) — tracedToSource, toolchainRuntime, toolchainHeader, unresolved
  Main.lean                   # CLI entry point (thin wrapper for CLI.run)
  Demo.lean                   # demos: standard, runtime externs, full, drill, multi-constant
```

Dependency chain: `Types ← Classify ← Traverse ← Monad ← Command`, `Types ← StackTrace ← Filter`, `Types ← ExternSourceProvenance`, `Filter + Traverse + Monad + ExternSourceProvenance ← CLI`.

Build targets: `lake build Lean4DepAudit` (library), `lake build Tests` (run 38 tests), `lake build audit` or `lake build` (CLI executable), `lake build demo` (elaboration-time demos).

---

## Design Decisions & Lessons Learned

### Why pure Environment, not MetaM?

We initially moved the first pass into `MetaM` with `withLocalDecl` at binder positions (`lam`, `forallE`, `letE`) so that `inferType` would work inside binder bodies. This caused heartbeat timeouts: 4300 constants × deep binder nesting = hundreds of thousands of `whnf` calls for zero benefit, since we never call `inferType` in the first pass.

`withLocalDecl` does real work — creates fresh fvars, extends the `LocalContext`, type-checks the binder type via `whnf` — and none of that is needed when you're just scanning for `.const` nodes, which are global references that never contain bound variables.

**Rule:** only use `MetaM` when you actually need the local context (e.g., `inferType`, `isDefEq`). For finding `.const` nodes, a pure `Environment`-based walk is sufficient and much faster.

### Why two passes?

The original single-pass design stored an `ExprPath` (full structural path from root) per finding encounter. This caused path explosion: extern constants like `Array.size` appear 1.5 million times across all 4300 constant bodies. Storing a path per encounter blew up both memory and time.

The key insight: the developer doesn't need all paths up front. They need (1) a summary of what's interesting and (2) a way to drill into specific findings on demand.

**Pass 1** is optimized for speed: no paths, just flags and a DAG. **Pass 2** is optimized for precision: answers "which of X's deps lead to Y?" instantly via set intersection on the pre-computed DAG.

### Why reverseDeps (child → {parents}) not forward deps?

The user's query starts at the finding (child) and asks "how do I get here from root?" The BFS in `findAncestors` walks upward from the target through parents to find all constants that transitively reach it. This direction is natural for `child → {parents}` and would require reversing the whole graph for `parent → {children}`.

Forward deps are computed on-the-fly by `immediateDeps` (a single `foldConsts` call) only when needed.

### Why not store paths in the DAG?

Enumerating all paths from root to target is combinatorially explosive (diamond dependencies in the DAG). For `propext` with 1213 encounters, there could be millions of distinct constant chains. Nobody wants to read them.

Instead, `drillDown` answers the actionable question: "which of my direct dependencies are responsible?" The developer can iterate level by level, which is both tractable and useful for debugging.

### Performance: `#audit` command vs CLI

The `#audit` command runs at elaboration time. When a custom config is provided via `with`, the config expression is evaluated using `evalExpr`, which uses the Lean **interpreter**. The resulting config closures (`shouldReport`, `shouldDescend`) are interpreted closures. When the compiled `auditConst` core calls these closures millions of times, each call crosses from compiled code into the interpreter — this is the primary performance bottleneck (~27s for a full traversal).

The standard config without `with` also runs at elaboration time but avoids `evalExpr`. Performance is still limited by the fact that the whole pipeline runs during elaboration.

**The `#audit` command is best for localized hints in Lean scripts.** For bulk audits and full-speed execution, the planned CLI executable (`lake exe audit`) will run everything as compiled native code — no interpreter overhead.

### Standard config design

The default `AuditConfig.standard` is designed for the primary use case: "does my project have any non-standard trust assumptions?"

- **Skips stdlib traversal** (module-based, not name-based): `IO.getStdin` lives in module `Init.System.IO`, so we check the module prefix, not the constant's namespace
- **Skips standard axioms**: `propext`, `Quot.sound`, `Classical.choice` are foundations, not trust concerns
- **Reports non-standard axioms**: custom `axiom` declarations indicate dismissed proof obligations
- **Reports non-standard runtime externs**: user `@[extern]` bindings are real trust boundaries
- **Skips proof descent**: kernel-time dependencies (Omega, decidability) are noise for most users

For a project that only uses the Lean standard library, this correctly reports 0 findings. Custom externs and axioms light up immediately.

### Opaque sub-classification

Lean 4 uses `opaque` in the Environment for several distinct purposes. We detect and sub-classify them:
- **`partial_`**: value has actual body structure (lambdas, lets) — it's a `partial def`
- **`initialize_`**: has `[init]` attribute or is `isIOUnitInitFn` — runtime init ref
- **`implementedBy_`**: value is `@default T inst` but no init attr — `NonemptyType` implementation
- **`other`**: catch-all — if users hit this, they report it and we add a category

---

## Runtime vs Kernel-time

Every `FindingInfo` carries `reachableAtRuntime` and `reachableInProof` flags:
- **Runtime** (`reachableAtRuntime = true`): externs/opaques your compiled binary calls
- **Kernel-time** (`reachableInProof = true`): externs/axioms the kernel evaluates during type-checking (e.g. `Lean.Omega` proof machinery using `Int.ediv`, `Nat.gcd`)

A constant can be both (e.g., `Array.push` is used in runtime code and in proof automation).

Both are real dependencies with real trust assumptions — they just answer different questions ("what C code does my binary link?" vs "what C code does the kernel trust when checking proofs?").

---

## How Custom FFI Works in Lean 4

Understanding the linking story is essential for extern symbol tracing. There are three ways developers bring custom native code into Lean projects:

### Approach 1: `extern_lib` target (build C from source)

The standard pattern. Requires `lakefile.lean` (TOML can't express this):

```lean
target ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "ffi.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  buildO oFile srcJob flags #[] "cc"

extern_lib libffi pkg := do
  let name := nameToStaticLib "ffi"
  let ffiO ← fetch <| pkg.target ``ffi.o
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]
```

The C file `#include <lean/lean.h>` and exports functions matching the `@[extern "symbol_name"]` strings. Lake compiles `.c` → `.o` → `.a`, and links the archive into executables.

**Discoverable:** The `.a` file ends up in `.lake/build/lib/`. We can `nm` it to find which symbols it provides.

### Approach 2: `moreLinkArgs` (link system library)

For already-installed system libraries:

```lean
package myProject where
  moreLinkArgs := #["-lglfw", "-L/usr/local/lib", "-lmylib"]
```

**Discoverable:** The `-l` and `-L` flags are in the lakefile. We can search those paths with `nm`.

### Approach 3: Alloy (inline C in .lean files)

The Alloy library embeds C directly in `.lean` files:

```lean
alloy c extern def myAdd (x y : UInt32) : UInt32 := { return x + y; }
```

Generates symbols with `_alloy_c_l_` prefix. The C code lives in the `.lean` file itself.

### Three categories of extern symbols in a linked executable

| Category | Where it lives | Example | Provenance |
|----------|---------------|---------|------------|
| **Header-only** (`static inline` in `lean.h`) | Inlined at compile time, no `.so` symbol | `lean_nat_add`, `lean_nat_dec_le` | `toolchainHeader` |
| **Runtime library** (in `libleanrt.a` / `libleanshared.so`) | Toolchain `lib/lean/` directory | `lean_string_append`, `lean_array_push` | `toolchainRuntime` |
| **User/project library** (in `.lake/build/lib/*.a`) | Project build directory | `test_ffi_add` (from extern_lib) | `tracedToSource` (if `.c` found via trace files) |

### What's available at elaboration time

- `getExternAttrData? env name` → the symbol name string (already used by `Classify.lean`)
- `searchPathRef.get` → search path directories (needs `IO`)
- `env.getModuleIdxFor? name` → which module a constant is from (determines stdlib vs user)

What's NOT available without shelling out:
- Which specific library file provides a given symbol — **now resolved by `nm` in `ExternSourceProvenance.lean`**
- Whether a symbol is header-only or a real linked symbol — **now resolved by scanning `lean.h`**
- Lake build configuration (`moreLinkArgs`, `extern_lib` targets) — Lake doesn't expose this as structured metadata; `ExternLibConfig.getPath` is an opaque closure
- **However:** Lake's build trace files (`.trace` JSON) record the full input→output chain for every artifact. `ExternSourceProvenance.lean` reads these to trace `.a` → `.o` → `.c` source paths without needing Lake's internal APIs

---

## Next Steps

### 1. CLI executable (`lake exe audit`) ✅

Done. Fully compiled native executable. Loads `.olean` files via `importModules`, runs `auditConst` natively. Usage:

```bash
lake exe audit myMain --import MyModule                     # standard config (default)
lake exe audit myMain --import MyModule --config full       # all findings
lake exe audit myMain --import MyModule --config runtimeExterns
lake exe audit myMain otherConst --import MyModule          # multiple constants
lake exe audit myMain --import MyModule --drill propext     # drill-down
lake exe audit myMain --import MyModule --report 'externs & !stdlib' --descend skipProofs
```

**Filter DSL** — a mini-expression language for composing filter predicates from the command line:
- Report atoms: `axioms`, `opaques`, `partials`, `externs`, `initialize`, `runtime`, `kernel`, `stdlib`, `hasFinding`, `nonStdAxioms`, `nonStdExterns`, `nonStdOpaques`
- Descend atoms: `skipProofs`, `skipTypes`, `all`
- Operators: `&` (and), `|` (or), `!` (not), `()` (grouping)
- Examples: `'externs & runtime'`, `'nonStdAxioms | nonStdExterns & !stdlib'`, `'!(axioms | opaques)'`

Hand-rolled recursive descent parser (~160 lines). Produces compiled `ConstContext → Bool` / `DescendContext → Bool` closures at startup — no interpreter overhead at audit time.

Named presets via `--config`: `standard` (default), `full`, `runtimeOnly`, `runtimeExterns`, `axiomsOnly`. Individual `--report`/`--recurse`/`--descend` flags override the preset's corresponding predicate.

**Files:**
- `Lean4DepAudit/CLI.lean` — tokenizer, recursive descent parser, arg parser, formatters, `run` entry point
- `Main.lean` — thin wrapper: `def main := CLI.run`
- `Demo.lean` — former `Main.lean` demos (now a separate `lake exe demo` target)

**Build targets:**
- `lake build audit` or `lake build` — builds the CLI executable
- `lake exe audit --help` — usage info

### 2. Record the constant's declared type ✅

Done. Each `FindingInfo` now stores the constant's declared (polymorphic) type as `type : Expr`, plus a pretty-printed `typeStr : String` populated by `resolveLocations` via `ppExpr`.

Output now shows types inline: `testExternFn [extern "test_c_fn"] [runtime] : Nat → Nat`. This tells you the API surface of each finding without requiring instantiation tracking (which would explode for polymorphic constants like `id` or `Array.size`).

**Design decision:** We store the declared type (`ci.type`), not instantiated types. Collecting all instantiations was rejected because a single polymorphic constant can be instantiated thousands of times (e.g., `id` at every type). The declared type is sufficient — it shows what the extern/axiom/opaque promises.

**Files changed:** `Types.lean` (new fields), `Traverse.lean` (record `ci.type` + pretty-print in `resolveLocations`), `CLI.lean` + `Command.lean` (formatters display type), `Tests/Helpers.lean` (new `assertHasType`/`assertTypeStrContains`), `Tests/TestTypeInfo.lean` (5 new tests).

**Tests:** 38 unit tests pass (29 original + 5 type-info + 4 provenance tests), 31 CLI integration tests pass (26 original + 5 provenance).

### 3. Extern symbol tracing + package-level test infrastructure

Trace each `@[extern]` symbol back to its native implementation. This is the auditor's core value proposition for real projects — answering "what C code does my binary actually link?"

#### 3a. Convert to `lakefile.lean` ✅

Done. The main project switched from `lakefile.toml` to `lakefile.lean` to support `extern_lib` targets and `require` local path dependencies.

#### 3b. Package-level test fixtures ✅

Done. Created `test-packages/ffi-fixture/` — a real Lake package with:
- `c/ffi.c` — three C functions: `test_ffi_add` (UInt32 addition), `test_ffi_toggle` (Bool negation), `test_ffi_const42` (thunk returning 42)
- `FfiFixture/Basic.lean` — `@[extern]` opaque declarations + pure Lean callers (`callsFfiAdd`, `callsBothFfi`, `ffiChainRoot`)
- `lakefile.lean` — `extern_lib` target: `c/ffi.c` → `ffi.o` → `libffi.a`, with `precompileModules := true`
- `Tests/TestFfi.lean` — 7 tests: extern classification with correct symbols, transitive detection, multi-extern, drill-down through FFI chains, standard config, reachability flags, thunk pattern

The root project's `lakefile.lean` declares `require FfiFixture from "test-packages" / "ffi-fixture"`. Build produces `libffi.a` with verified symbols (`nm` confirms all three). All 29 tests pass (22 original + 7 FFI).

**What this exercises:**
- Constants where the extern symbol resolves to a user-compiled `.a` in `.lake/build/`
- The `extern_lib` target build chain: `.c` → `.o` → `.a` → linked
- Distinction between user extern symbols (in the fixture package) and stdlib symbols (in the toolchain)
- `precompileModules` for interpreter-time resolution

**Additional fixture packages to consider:**
- A package using `moreLinkArgs` to link a system library (e.g., `-lm` for `sin`/`cos`)
- A package using the Alloy approach (inline C in `.lean` files) if we want to detect that pattern

#### 3c. Symbol provenance resolution ✅

Done. Each extern `FindingInfo` now carries a `provenance? : Option SymbolProvenance` field, populated by `resolveProvenance : AuditResult → SearchPath → IO AuditResult`. This is a post-processing step that runs after `resolveLocations`, in `IO` (no `MetaM`).

**`SymbolProvenance` type:**
```lean
inductive SymbolProvenance where
  | tracedToSource (cFile : String) (oFile : String) (aFile : String)  -- full trust chain
  | toolchainRuntime (lib : String)    -- found in libleanrt.a
  | toolchainHeader                     -- static inline in lean.h
  | unresolved                          -- not found anywhere, sus
```

**Resolution strategy (implemented in `ExternSourceProvenance.lean`):**
1. Compute library directories from `searchPathRef` entries (each entry + parent, plus toolchain `lib/lean/`)
2. Build symbol → `.a` index by running `nm --defined-only` on all `.a` files found
3. For each extern finding, look up the symbol:
   - Found in toolchain `libleanrt.a` → `toolchainRuntime`
   - Found in a project/package `.a` → trace through Lake build artifacts:
     - Read `.a.trace` → get `.o` file paths
     - Run `nm` on each `.o` to find which one contains the symbol
     - Read matching `.o.trace` → get `.c` source path
     - Verify `.c` exists on disk → `tracedToSource cFile oFile aFile`
   - Not found in any `.a` → check `lean.h` for `static inline` → `toolchainHeader` or `unresolved`

**Verified results:**
- FFI fixture `test_ffi_add` → `tracedToSource "…/ffi-fixture/c/ffi.c" "…/ffi.o" "…/libffi.a"`
- Stdlib `lean_array_push` → `toolchainRuntime "…/libleanrt.a"`
- Stdlib `lean_nat_dec_le` → `toolchainHeader`

**Serializable types:** `SymbolProvenanceSer` with `deriving ToJson, FromJson`, `provenance?` field on `FindingInfoSer`. JSON round-trips correctly.

**YAML output** shows provenance per extern finding:
```yaml
provenance: traced "/path/to/c/ffi.c"
provenance: toolchain-runtime "/path/to/libleanrt.a"
provenance: toolchain-header
provenance: UNRESOLVED
```

**CLI integration:** `resolveProvenance` runs automatically in `CLI.run` after `resolveLocations`. All 38 unit tests + 31 CLI integration tests pass.

**Files:** `Lean4DepAudit/ExternSourceProvenance.lean` (new, 248 lines), `Types.lean` (updated), `CLI.lean` (updated), `Lean4DepAudit.lean` (updated import).

**Design note:** The original plan had 6 variants (`toolchainModule`, `projectLib`, `systemLib`). The implementation simplified to 4 variants focused on the core audit question: "can I trace this to readable source code?" The `tracedToSource` variant records the full chain (`.c`, `.o`, `.a`), while the toolchain variants are known-trusted. Anything else is `unresolved` = sus. The `toolchainModule` distinction (libInit.a vs libleanrt.a) was dropped because both are toolchain-trusted. `systemLib` (from `moreLinkArgs`) was deferred — we'd need to parse lakefile link flags, which we explicitly decided not to do.

#### 3d. Tests for symbol tracing ✅

Done. 4 unit tests in `Tests/TestProvenance.lean` + 5 CLI tests in `TestCLI.lean`, covering all 4 active `SymbolProvenance` constructors.

**Unit tests (`Tests/TestProvenance.lean`):**
- `tracedToSource`: audit `FfiFixture.callsFfiAdd` → `FfiFixture.ffiAdd` provenance contains `ffi.c`
- `toolchainRuntime`: audit `String.append` → at least one extern finding with `toolchainRuntime` provenance (e.g., `ByteArray.mk` → `lean_byte_array_mk` in `libleanrt.a`)
- `toolchainHeader`: same audit → at least one extern finding with `toolchainHeader` provenance (e.g., `UInt32.toBitVec` → `lean_uint32_to_nat`, `static inline` in `lean.h`)
- `unresolved`: audit `TestFixtures.Extern.testCallsExtern` → `testExternFn` with symbol `test_c_fn` has no backing native code

**CLI tests (`TestCLI.lean`):**
- YAML: `provenance: UNRESOLVED` for user extern, `provenance: toolchain-runtime` and `provenance: toolchain-header` for stdlib externs
- JSON: user extern has `unresolved` provenance, all stdlib externs have provenance populated

**Test helpers added to `Tests/Helpers.lean`:**
- `runAuditWithProvenance` — runs `auditConst` + `resolveLocations` + `resolveProvenance` (needs IO for `nm`/trace scanning)
- `assertProvenanceMatches` — generic predicate-based provenance assertion
- `assertTracedToSource`, `assertToolchainRuntime`, `assertToolchainHeader`, `assertUnresolved` — constructor-specific assertions

**`binaryOnly` edge case:** Shelved. See `extern-provenance-findings.md` for the full investigation. The `binaryOnly` constructor is commented out with TODO placeholders across `Types.lean`, `ExternSourceProvenance.lean`, and `CLI.lean`. Key finding: Lean FFI always requires a C wrapper at the boundary (for `lean_object*` conventions), so a Lake-built `extern_lib` always has trace files. The `moreLinkObjs` + `input_file` pattern for pre-built `.a` files doesn't compose with `precompileModules := true` (per-module dynlibs don't include `moreLinkObjs`). A commented-out `harvestLinkedLibraries` function in `ExternSourceProvenance.lean` contains the trace-scanning logic for when this is resolved.

**Tests:** 38 unit tests pass, 31 CLI integration tests pass.

---

## Key Files to Read

- **`Lean4DepAudit/Types.lean`** — all data types: OpaqueKind, Finding, FindingInfo, AuditResult, DrillResult, AuditConfig
- **`Lean4DepAudit/Classify.lean`** — constant classification (axiom/opaque sub-kind/extern)
- **`Lean4DepAudit/Traverse.lean`** — pass 1 (auditConst), pass 2 (drillDown), resolveLocations
- **`Lean4DepAudit/Monad.lean`** — AuditM monad, monadic wrappers
- **`Lean4DepAudit/Command.lean`** — `#audit` command elaborator
- **`Lean4DepAudit/Filter.lean`** — composable filter/descent predicates, stdlib detection, convenience configs
- **`Lean4DepAudit/ExternSourceProvenance.lean`** — IO-based extern symbol → C source tracing via Lake trace files (`nm`, `.trace` JSON, `lean.h` scanning)
- **`Lean4DepAudit/CLI.lean`** — CLI: filter DSL parser, arg parser, formatters, `run` entry point
- **`Lean4DepAudit/StackTrace.lean`** — compile-time stack trace rendering
- **`test-packages/ffi-fixture/`** — real Lake package with C FFI (extern_lib, libffi.a)
- **`test-packages/ffi-fixture/c/ffi.c`** — C implementations for test extern symbols
- **`test-packages/ffi-fixture/FfiFixture/Basic.lean`** — @[extern] bindings + callers
- **`TestFixtures/`** — in-project test fixture constants (Extern, Axiom, Opaque, PureStdlib, Chain)
- **`Tests/Helpers.lean`** — assertion helpers, `runTest`, `runAudit` wrappers
- **`Tests/Test*.lean`** — 38 tests across 9 test files (including TestFfi.lean for real FFI, TestTypeInfo.lean for declared types, TestProvenance.lean for symbol provenance)
- **`Main.lean`** — CLI entry point (`def main := CLI.run`)
- **`Demo.lean`** — five demos: standard, runtime externs, full, drill, multi-constant
- **`opencode.json`** — MCP server config (lean-lsp-mcp)
- **`.opencode/skills/lean4/SKILL.md`** — lean4 skill (loaded via `skill` tool)

## Lean API Reference (for Lean 4.29.0)

- `Lean.Environment.find? : Environment → Name → Option ConstantInfo`
- `Lean.ConstantInfo` — `.axiomInfo`, `.defnInfo`, `.thmInfo`, `.opaqueInfo`, `.inductInfo`, `.ctorInfo`, `.recInfo`, `.quotInfo`
- `Lean.ConstantInfo.value? : ConstantInfo → Option Expr` — returns value for defn/thm/opaque
- `Lean.OpaqueVal` — has `value : Expr`, `isUnsafe : Bool`, `all : List Name`
- `Lean.isExtern : Environment → Name → Bool`
- `Lean.getExternAttrData? : Environment → Name → Option ExternAttrData`
- `ExternAttrData.entries : List ExternEntry`
- `ExternEntry` — `.adhoc name`, `.inline name str`, `.standard name str`, `.opaque`
- `Lean.hasInitAttr : Environment → Name → Bool` — detects `[init]` attribute
- `Lean.isIOUnitInitFn : Environment → Name → Bool` — detects `initialize` declarations
- `Lean.isIOUnitBuiltinInitFn : Environment → Name → Bool` — detects `builtin_initialize`
- `Lean.Name.isPrefixOf : Name → Name → Bool` — built-in, no need to redefine
- `Lean.Expr.foldConsts : Expr → α → (Name → α → α) → α` — fast built-in scan for all `.const` names in an expression
- `Lean.findDeclarationRanges? : Name → m (Option DeclarationRanges)` — source location lookup (needs `MonadEnv + MonadLiftT BaseIO`)
- `Lean.Environment.getModuleIdxFor? : Environment → Name → Option ModuleIdx` — which module a constant is from

## Tools Available

- **lean-lsp-mcp** via OpenCode MCP — `lean_diagnostic_messages`, `lean_goal`, `lean_hover_info`, `lean_run_code`, `lean_multi_attempt`, `lean_build`, etc.
- **lean4 skill** — loaded via the `skill` tool, provides proving/reviewing/refactoring workflows
- Build with `lake build` (inside nix shell or via direnv)
