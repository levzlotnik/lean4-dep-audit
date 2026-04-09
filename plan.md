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

### Core Auditor (working)

**`MyLeanTermAuditor/Audit.lean`** — the auditor is implemented and working:

- `Finding` — inductive: `axiom_`, `opaque_`, `extern_ (sym : String)`
- `ExprStep` — inductive: 13 variants for path tracking (`appFn`, `appArg`, `lamType`, `lamBody`, `forallType`, `forallBody`, `letType`, `letVal`, `letBody`, `mdata`, `proj`, `constDef name`, `constType name`)
- `ExprPath` — abbreviation for `Array ExprStep`, with `ToString`, `toFrames`, `toStackTrace`, `toCompactTrace`
- `StackFrame` — struct: constant name, isDef, localSteps within that frame
- `AuditEntry` — struct: `name`, `finding`, `path`, `inProofTerm`
- `AuditResult` — struct: `entries : Array AuditEntry`, `visited : NameHashSet`
- `ConstContext` — rich predicate context: `env`, `name`, `ci`, `path`, `levels`, `finding`, `inProofTerm`
- `DescendContext` — structural predicate context: `step`, `path`, `currentConst?`, `inProofTerm`
- `AuditConfig` — three predicates:
  - `shouldRecurse : ConstContext → Bool` — controls traversal at constant boundaries
  - `shouldReport : ConstContext → Bool` — controls what appears in output
  - `shouldDescend : DescendContext → Bool` — controls traversal at structural positions
- `TraversalState` — threads `currentConst?` and `inProofTerm` through recursion
- `isTheorem` — helper to detect `.thmInfo` constants
- `getExternSymbol?` — extracts extern symbol from `ExternAttrData.entries`
- `classifyConst` — classifies `ConstantInfo` as interesting or not
- `auditExpr` — partial recursive `Expr` walker with path tracking, proof-term detection, and three-predicate filtering
- `auditConst` — entry point: looks up a name in the `Environment`, audits its type and value

**Filter combinators** (`Filter` namespace):
- `byName`, `inNamespaces`, `notInNamespaces` — name-based filtering
- `axiomsOnly`, `opaquesOnly`, `externsOnly` — finding-type filters
- `runtimeOnly`, `kernelOnly` — runtime vs kernel-time classification
- `maxDepth`, `pathThrough`, `hasAnyFinding` — structural filters
- `and`, `or`, `not` — boolean combinators

**Descent combinators** (`Descend` namespace):
- `skipProofTerms` — prunes entire proof subtree (theorem values)
- `skipTypes` — skips `forallType`/`lamType`/`letType` positions
- `all` — default, descend everywhere
- `and`, `or` — boolean combinators

**Convenience configs**:
- `AuditConfig.default` — recurse everywhere, report everything
- `AuditConfig.trustPrefixes` — skip recursing into given namespaces
- `AuditConfig.runtimeOnly` — skip proof terms, report runtime deps
- `AuditConfig.runtimeExterns` — skip proof terms, report only runtime externs
- `AuditConfig.axiomsOnly` — report only axioms

**`Main.lean`** — three demo audits of `myMain : IO Unit`:

1. **Full audit**: 4300 constants visited, 91 findings (3 axioms, 6 opaques, 82 externs) — all with `[kernel-time]` tags where applicable
2. **Runtime externs**: 703 constants visited, 56 externs — proof machinery eliminated
3. **Runtime all**: 703 constants visited, 60 findings (4 opaques, 56 externs)

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
  MyLeanTermAuditor.lean      # root import (imports Basic + Audit)
  MyLeanTermAuditor/
    Basic.lean                # placeholder (from lake init)
    Audit.lean                # core auditor + filtering + stack traces
  Main.lean                   # demo: three #eval audits of myMain
  Explore.lean                # scratch file for API exploration (can delete)
```

---

## Design: Core Auditor

### Traversal

Walk `Expr` recursively. At every `Expr.const name levels`:
1. Skip if already in visited set (cycle detection)
2. Look up `name` in `Environment` via `env.find?`
3. Classify via `classifyConst` (axiom/opaque/extern or uninteresting)
4. Build `ConstContext` with full info (env, name, ci, path, levels, finding, inProofTerm)
5. If `shouldReport cctx`, add to entries (with path and `inProofTerm` flag)
6. If `shouldRecurse cctx`, recurse into `ci.type` and `ci.value?`
   - When entering a theorem's value, flip `inProofTerm` to `true`

At every structural position (app, lam, forall, let, mdata, proj):
7. Build `DescendContext` with step, path, currentConst?, inProofTerm
8. If `shouldDescend dctx`, recurse into the subexpression

All state is threaded via `TraversalState` (currentConst?, inProofTerm) and `AuditResult` (entries, visited).

### Configuration

Three predicates, all caller-supplied via `AuditConfig`:
- `shouldRecurse : ConstContext → Bool` — enter this constant's definition/type?
- `shouldReport : ConstContext → Bool` — include this in the output?
- `shouldDescend : DescendContext → Bool` — recurse into this subexpression?

These are independent and composable via the `Filter`/`Descend` combinator libraries.

### Runtime vs Kernel-time

Every `AuditEntry` carries `inProofTerm : Bool`:
- **Runtime** (`inProofTerm = false`): externs/opaques your compiled binary calls
- **Kernel-time** (`inProofTerm = true`): externs/axioms the kernel evaluates during type-checking (e.g. `Lean.Omega` proof machinery using `Int.ediv`, `Nat.gcd`)

Both are real dependencies with real trust assumptions — they just answer different questions ("what C code does my binary link?" vs "what C code does the kernel trust when checking proofs?").

---

## Next Steps

### 1. `#audit` command

Create a command elaborator so users can write:
```lean
#audit myMain
#audit myMain (mode := .runtimeExterns)
#audit myMain (trust := [Init, Std])
```

Instead of the current `#eval` boilerplate. This is the biggest remaining DX win.

### 2. Record the constant's instantiated type at usage site

When we hit `.const name levels`, record the instantiated type: `ci.type.instantiateLevelParams ci.levelParams levels`. This is pure (no MetaM needed).

Tells us "this extern is being used as `Nat → Nat → Nat`" rather than just "this extern exists."

### 3. (Hard) Record the expected type at the usage site

What does the surrounding context expect at that position? This requires either:
- Running in `MetaM` and calling `inferType` on the subexpression, or
- Manually threading a local context through binders (lambdas/foralls/lets)

This would tell us "at this app argument, Lean expects a `Nat`, and `Nat.add` is providing `Nat → Nat → Nat`."

### 4. Extern symbol tracing (stretch)

For each extern symbol found, trace it back to the linked native library:
- Parse `lakefile.toml` for `moreLinkArgs`
- Find the `.a`/`.so` containing the symbol via `nm`/`objdump`
- Optionally find C source in the workspace

### 5. Admissibility proof (stretch)

Prove that `shouldReport cctx = true ∧ cctx.finding = some f → entry ∈ result.entries`. Should be straightforward from construction but would be a nice self-referential demonstration.

---

## Key Files to Read

- **`MyLeanTermAuditor/Audit.lean`** — all the auditor logic, filtering, stack traces
- **`Main.lean`** — three demo audits (full, runtime externs, runtime all)
- **`opencode.json`** — MCP server config (lean-lsp-mcp)
- **`.opencode/skills/lean4/SKILL.md`** — lean4 skill (loaded via `skill` tool)

## Lean API Reference (for Lean 4.29.0)

- `Lean.Environment.find? : Environment → Name → Option ConstantInfo`
- `Lean.ConstantInfo` — `.axiomInfo`, `.defnInfo`, `.thmInfo`, `.opaqueInfo`, `.inductInfo`, `.ctorInfo`, `.recInfo`, `.quotInfo`
- `Lean.ConstantInfo.value? : ConstantInfo → Option Expr` — returns value for defn/thm/opaque
- `Lean.isExtern : Environment → Name → Bool`
- `Lean.getExternAttrData? : Environment → Name → Option ExternAttrData`
- `ExternAttrData.entries : List ExternEntry`
- `ExternEntry` — `.adhoc name`, `.inline name str`, `.standard name str`, `.opaque`
- `Lean.Name.isPrefixOf : Name → Name → Bool` — built-in, no need to redefine

## Tools Available

- **lean-lsp-mcp** via OpenCode MCP — `lean_diagnostic_messages`, `lean_goal`, `lean_hover_info`, `lean_run_code`, `lean_multi_attempt`, `lean_build`, etc.
- **lean4 skill** — loaded via the `skill` tool, provides proving/reviewing/refactoring workflows
- Build with `lake build` (inside nix shell or via direnv)
