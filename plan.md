# MyLeanTermAuditor — Plan

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
- `FindingInfo` — struct: `name`, `finding`, `location`, `reachableAtRuntime`, `reachableInProof`, `numEncounters`
- `AuditResult` — struct: `findings`, `visited`, `reverseDeps`
- `DrillResult` — struct: `from_`, `target`, `children : List Name`
- `ConstContext` — lightweight predicate context: `env`, `name`, `ci`, `levels`, `finding`, `inProofTerm`, `depth`, `constStack`
- `DescendContext` — structural predicate context: `step`, `currentConst?`, `inProofTerm`
- `AuditConfig` — struct: `shouldRecurse`, `shouldReport`, `shouldDescend` (predicates) + `drill : List Name`

**`Classify.lean`:**
- `getExternSymbol?` — extracts extern symbol from `ExternAttrData.entries`
- `classifyOpaqueKind` — sub-classifies opaques using init attrs and value shape
- `classifyConst` — classifies `ConstantInfo` as interesting or not (externs take priority over opaques)

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

### Test Suite (22 tests, all passing)

Fixtures in `TestFixtures/` (separate `lean_lib`, compiled independently), tests in `Tests/` that import fixtures + auditor. `lake build Tests` = run all tests. Assertion failure = build error.

**Fixture files:**
- `TestFixtures/Extern.lean` — `@[extern "test_c_fn"]` binding, caller, dual-extern caller
- `TestFixtures/Axiom.lean` — custom `axiom`, `sorry`-based theorem, transitive sorry usage
- `TestFixtures/Opaque.lean` — `partial def`, plain `opaque`, callers for each
- `TestFixtures/PureStdlib.lean` — pure arithmetic, pure IO, list processing (all stdlib-only)
- `TestFixtures/Chain.lean` — known dependency chain with extern leaf for drill-down queries

**Test files (22 `run_cmd` blocks):**
- `Tests/TestExtern.lean` (5 tests) — extern classification, transitive detection, dual externs, standard config, reachability flags
- `Tests/TestAxiom.lean` (4 tests) — axiom classification, transitive detection, standard config, sorry → `sorryAx` (classified as `extern_ "lean_sorry"` since `@[extern]` takes priority)
- `Tests/TestOpaque.lean` (3 tests) — partial def, implementedBy classification, standard config
- `Tests/TestPureStdlib.lean` (4 tests) — 0 findings for pure code under standard config, >0 findings under default config (validates filtering isn't trivially empty)
- `Tests/TestDrillDown.lean` (4 tests) — single-path drill, multi-path drill, non-existent target, extern finding detection
- `Tests/TestMulti.lean` (3 tests) — shared visited dedup, disjoint trees, combined visit count ≥ individual

**Test infrastructure:**
- `Tests/Helpers.lean` — assertion helpers (`assertHasFinding`, `assertFindingIs`, `assertReachability`, `assertDrillContains`, etc.), `runAudit`/`runAuditMulti` wrappers, `runTest` lifts `MetaM` into `CommandElabM`

**Key finding:** `sorryAx` is classified as `extern_ "lean_sorry"` (not `axiom_`) because `sorryAx` has `@[extern "lean_sorry"]` in the Lean runtime, and the auditor's classification correctly gives extern priority over axiom.

### Project Structure

```
MyLeanTermAuditor/
  lakefile.toml
  lean-toolchain              # leanprover/lean4:v4.29.0
  flake.nix                   # nix dev shell with elan
  .envrc                      # direnv: `use flake`
  opencode.json               # lean-lsp-mcp config
  .opencode/skills/lean4/     # lean4-skills pack
  plan.md                     # this file
  MyLeanTermAuditor.lean      # root import (re-exports all modules)
  MyLeanTermAuditor/
    Basic.lean                # placeholder (from lake init)
    Types.lean                # OpaqueKind, Finding, FindingInfo, AuditResult, DrillResult, AuditConfig
    Classify.lean             # getExternSymbol?, classifyOpaqueKind, classifyConst
    Traverse.lean             # auditConst (pass 1), drillDown (pass 2), resolveLocations
    Monad.lean                # AuditM, monadic wrappers
    Command.lean              # #audit command elaborator
    StackTrace.lean           # StackFrame, toFrames, toStackTrace, DrillResult.toTraceString
    Filter.lean               # Filter/Descend combinators, standard library detection, convenience configs
  TestFixtures.lean           # root import for test fixtures
  TestFixtures/
    Extern.lean               # @[extern] bindings
    Axiom.lean                # custom axiom, sorry
    Opaque.lean               # partial def, plain opaque
    PureStdlib.lean           # stdlib-only code
    Chain.lean                # known dependency chain for drill-down
  Tests.lean                  # root import for tests
  Tests/
    Helpers.lean              # assertion helpers, runTest, runAudit wrappers
    TestExtern.lean           # extern tests (5)
    TestAxiom.lean            # axiom tests (4)
    TestOpaque.lean           # opaque tests (3)
    TestPureStdlib.lean       # pure stdlib tests (4)
    TestDrillDown.lean        # drill-down tests (4)
    TestMulti.lean            # multi-constant tests (3)
  Main.lean                   # demos: standard, runtime externs, full, drill, multi-constant
```

Dependency chain: `Types ← Classify ← Traverse ← Monad ← Command`, `Types ← StackTrace ← Filter`.

Build targets: `lake build MyLeanTermAuditor` (library), `lake build Tests` (run tests), `lake build` (everything including Main.lean demos).

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

## Next Steps

### 1. CLI executable (`lake exe audit`)

Build a compiled executable for bulk/CI audits:
```bash
lake exe audit myMain
lake exe audit myMain --config runtimeExterns
lake exe audit --module MyModule    # all public defs in a module
```

Fully compiled — no interpreter overhead. Loads `.olean` files, runs `auditConst` natively. The main performance path.

### 2. Record the constant's instantiated type at usage site

When we hit `.const name levels`, record the instantiated type: `ci.type.instantiateLevelParams ci.levelParams levels`. This is pure (no MetaM needed).

Tells us "this extern is being used as `Nat → Nat → Nat`" rather than just "this extern exists."

### 3. (Hard) Record the expected type at the usage site

What does the surrounding context expect at that position? This requires a third pass using `MetaM` + `withLocalDecl` + `inferType`, targeted at specific constants from the drill-down (not a full re-traversal).

### 4. Extern symbol tracing (stretch)

For each extern symbol found, trace it back to the linked native library:
- Parse `lakefile.toml` for `moreLinkArgs`
- Find the `.a`/`.so` containing the symbol via `nm`/`objdump`
- Optionally find C source in the workspace

### 5. Admissibility proof (stretch)

The traversal is `partial` because it follows `.const` references into the `Environment` (the new `Expr` is not structurally smaller). Termination is guaranteed by the `visited` set (at most `env.size` constants), but proving this in Lean requires well-founded recursion on `env.size - visited.size`. Could be done with a fuel parameter but would add noise to the code.

---

## Key Files to Read

- **`MyLeanTermAuditor/Types.lean`** — all data types: OpaqueKind, Finding, FindingInfo, AuditResult, DrillResult, AuditConfig
- **`MyLeanTermAuditor/Classify.lean`** — constant classification (axiom/opaque sub-kind/extern)
- **`MyLeanTermAuditor/Traverse.lean`** — pass 1 (auditConst), pass 2 (drillDown), resolveLocations
- **`MyLeanTermAuditor/Monad.lean`** — AuditM monad, monadic wrappers
- **`MyLeanTermAuditor/Command.lean`** — `#audit` command elaborator
- **`MyLeanTermAuditor/Filter.lean`** — composable filter/descent predicates, stdlib detection, convenience configs
- **`MyLeanTermAuditor/StackTrace.lean`** — compile-time stack trace rendering
- **`TestFixtures/`** — test fixture constants (Extern, Axiom, Opaque, PureStdlib, Chain)
- **`Tests/Helpers.lean`** — assertion helpers, `runTest`, `runAudit` wrappers
- **`Tests/Test*.lean`** — 22 tests across 6 test files
- **`Main.lean`** — five demos: standard, runtime externs, full, drill, multi-constant
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
