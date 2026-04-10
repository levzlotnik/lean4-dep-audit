# AGENTS.md

## Developer Commands
- Build library only: `lake build MyLeanTermAuditor`
- Build everything (including Main.lean demos): `lake build`
- Run executable: `lake exe myleantermauditor` (placeholder — real output is from `#eval` at elaboration time)

## Verification
- **Primary**: Check for Lean compiler diagnostics (errors/warnings) via LSP.
- **Logic Testing**: Add `#eval` blocks in `.lean` files (e.g., `Main.lean`) to verify auditor results during elaboration.
- **Build Check**: Run `lake build MyLeanTermAuditor` for fast iteration (skips Main.lean's expensive `#eval` blocks). Run `lake build` for full verification.
- **Profiling**: Add `set_option profiler true` before `#eval` blocks to see interpretation vs elaboration time.

## Architecture

Read `plan.md` for the full design document. Key points below.

### Two-Pass Design

**Pass 1 (`auditConst`):** Pure function `Environment → AuditConfig → Name → AuditResult`. Walks all reachable constants, classifies findings (axiom/opaque/extern), records reachability flags, builds the reverse dependency DAG. No MetaM, no paths, no IO.

**Pass 2 (`drillDown`):** Pure function `Environment → Name → Name → AuditResult → DrillResult`. Answers "which direct deps of X lead to target Y?" via set intersection on the pre-computed DAG. Instant.

**`resolveLocations`:** `AuditResult → MetaM AuditResult`. Optional post-processing that fills in source locations. The only part that needs MetaM.

### Critical Constraints

**Do not add MetaM to the first pass.** Every attempt caused severe performance problems:
- `withLocalDecl` triggers `whnf` at every binder, causing heartbeat timeouts on 4300 constants
- `StateT AuditResult MetaM` copies the entire result struct on every `modify` call
- The first pass only scans for `.const` nodes, which are global references that never contain bound variables — `MetaM`'s local context management is pure overhead here

**Do not store paths in the first pass.** Extern constants like `Array.size` appear 1.5 million times across all constant bodies. Storing an `ExprPath` per encounter causes memory/time explosion. The first pass records only flags and encounter counts.

**`reverseDeps` is `child → {parents}`, not forward deps.** The user queries start at findings and walk upward to the root. Don't flip the direction.

**The interpreter is the bottleneck.** `set_option profiler true` shows `interpretation 55.6s` for `#eval` blocks, with elaboration under 500ms. The highest-impact improvement is a compiled `#audit` command.

### Module Dependency Chain

```
Types ← Classify ← Traverse
Types ← StackTrace ← Filter
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
    │                    AuditResult (with source locations filled in)
    │                         │
    ▼                         ▼
drillDown (pure)  ◄──  AuditResult
    │
    ▼
DrillResult { from_, target, children }
```

## Working with the Owner

- Has strong opinions about data structure design — explain your reasoning before implementing
- Prefers power over minimalism — "we can break shit to build better shit"
- Will push back on unnecessary complexity and wrong abstractions
- Values honest technical assessment over validation
