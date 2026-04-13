# AGENTS.md

## Developer Commands
- Build library only: `lake build Lean4DepAudit`
- Run tests (38 tests): `lake build Tests`
- Run CLI integration tests (31 tests): `lake build audit && lake build test_cli && lake exe test_cli`
- Build CLI executable: `lake build audit` (or `lake build`, it's the default target)
- Build demos: `lake build demo`
- Run CLI: `lake exe audit <constant> --import <module> [--config standard|full|...] [--report <dsl>] [--drill <name>]`
- CLI help: `lake exe audit --help`

## Verification
- **Primary**: Check for Lean compiler diagnostics (errors/warnings) via LSP.
- **Test Suite**: Run `lake build Tests` — 38 `run_cmd` tests across 9 files. Build failure = test failure.
- **Logic Testing**: Add `#eval` blocks in `.lean` files (e.g., `Main.lean`) to verify auditor results during elaboration.
- **Build Check**: Run `lake build Lean4DepAudit` for fast iteration (skips Main.lean's expensive `#eval` blocks). Run `lake build` for full verification.
- **Profiling**: Add `set_option profiler true` before `#eval` blocks to see interpretation vs elaboration time.

## Test Architecture
- **Fixtures** (`TestFixtures/`): Separate `lean_lib` with constants that have specific characteristics (extern, axiom, opaque, pure stdlib, dependency chains). Compiled independently — never rebuilt unless fixtures change.
- **FFI Fixture** (`test-packages/ffi-fixture/`): Real Lake package with C source compiled via `extern_lib`. The root project depends on it via `require`. Tests import `FfiFixture` and audit constants backed by real linked native code (`libffi.a` with symbols `test_ffi_add`, `test_ffi_toggle`, `test_ffi_const42`).
- **Tests** (`Tests/`): Import fixtures + `FfiFixture` + `Lean4DepAudit`. Each `run_cmd` block calls `auditConst`/`drillDown` directly (pure functions, take `Environment`) and asserts on the `AuditResult`. Assertion failure = build error.
- **Helpers** (`Tests/Helpers.lean`): `assertHasFinding`, `assertFindingIs`, `assertReachability`, `assertDrillContains`, `assertNumFindings`, `assertHasType`, `assertTypeStrContains`, `runAudit`, `runAuditMulti`, `runTest` (lifts MetaM → CommandElabM).

## Architecture

Read `plan.md` for the full design document. Key points below.

### Two-Pass Design

**Pass 1 (`auditConst`):** `Environment → AuditConfig → Name → AuditResult`. Walks all reachable constants, classifies findings (axiom/opaque/extern), records reachability flags, builds the reverse dependency DAG.

**Pass 2 (`drillDown`):** `Environment → Name → Name → AuditResult → DrillResult`. Answers "which direct deps of X lead to target Y?" via set intersection on the pre-computed DAG.

**`resolveLocations`:** `AuditResult → MetaM AuditResult`. Optional post-processing that fills in source locations and pretty-prints declared types.

**`resolveProvenance`:** `AuditResult → SearchPath → IO AuditResult`. Post-processing that traces each `@[extern]` symbol back to its C source through Lake's build trace files. Shells out to `nm`, reads `.trace` JSON, scans `lean.h`. Classifies as `tracedToSource` (full chain to `.c`), `toolchainRuntime` (in `libleanrt.a`), `toolchainHeader` (`static inline` in `lean.h`), or `unresolved` (sus).

### Critical Constraints

**Do not store paths in the first pass.** Extern constants like `Array.size` appear 1.5 million times across all constant bodies. Storing an `ExprPath` per encounter causes memory/time explosion. The first pass records only flags and encounter counts.

**`reverseDeps` is `child → {parents}`, not forward deps.** The user queries start at findings and walk upward to the root. Don't flip the direction.

**The interpreter is the bottleneck.** `set_option profiler true` shows `interpretation 55.6s` for `#eval` blocks, with elaboration under 500ms. The highest-impact improvement is a compiled `#audit` command.

### Module Dependency Chain

```
Types ← Classify ← Traverse
Types ← StackTrace ← Filter
Types ← ExternSourceProvenance
```

### What's Currently Unused

`ExprPath`, `ExprStep`, `StackFrame`, and the stack trace rendering in `StackTrace.lean` are defined but not consumed by either pass. They exist for a future third pass that does targeted `Expr`-level path collection with `MetaM` + `withLocalDecl`, scoped to ancestors of a specific target. Don't delete them, but don't assume they're tested against current data structures.

### Data Flow

```
Environment
    │
    ▼
auditConst (pure)  ──►  AuditResult { findings, visited, reverseDeps }
    │                         │
    │                         ▼
    │                    resolveLocations (MetaM, optional)
    │                         │
    │                         ▼
    │                    resolveProvenance (IO, optional)
    │                         │
    │                         ▼
    │                    AuditResult (with source locations + provenance filled in)
    │                         │
    ▼                         ▼
drillDown (pure)  ◄──  AuditResult
    │
    ▼
DrillResult { from_, target, children }
```

## Shell Rules

- **NEVER use heredocs** (`<< EOF`, `<< 'EOF'`, etc.) in Bash commands. Write files using the Write tool instead.

## Working with the Owner

- Has strong opinions about data structure design — explain your reasoning before implementing
- Prefers power over minimalism — "we can break shit to build better shit"
- Will push back on unnecessary complexity and wrong abstractions
- Values honest technical assessment over validation
