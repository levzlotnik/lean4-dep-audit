# MyLeanTermAuditor — Plan

## Goal

Build a Lean 4 metaprogram that traverses any `Expr` (including `IO` terms like `main`) and produces a structured audit report of its transitive dependencies — focusing on axioms, opaques, and `@[extern]` FFI bindings.

## Why

Lean's `#print axioms` only reports axioms and only at the command level. We want:

- Full classification: axioms, opaques, externs, inductives, etc.
- Pointed at arbitrary terms, including IO actions
- Configurable trust boundaries (ignore Init/Std/Lean by default, audit everything if asked)
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
- `AuditEntry` — struct: `name : Name`, `finding : Finding`
- `AuditResult` — struct: `entries : Array AuditEntry`, `visited : NameHashSet`
- `AuditConfig` — struct with two predicates:
  - `shouldRecurse : Name → Bool` — controls traversal depth
  - `shouldReport : Name → Bool` — controls what appears in output
- `AuditConfig.trustPrefixes` — convenience constructor using `Name.isPrefixOf`
- `getExternSymbol?` — extracts extern symbol from `ExternAttrData.entries` (supports `.standard` and `.inline` entries)
- `classifyConst` — classifies `ConstantInfo` as interesting or not
- `auditExpr` — partial recursive `Expr` walker with visited set for cycle detection
- `auditConst` — entry point: looks up a name in the `Environment`, audits its type and value

**`Main.lean`** — experiment that audits a sample `myMain : IO Unit` at elaboration time via `#eval`:

- `myMain` reads a line from stdin and prints a greeting
- The `#eval` runs in `CommandElabM`, gets the environment, and calls `auditConst`
- **Results: 4300 constants visited, 91 interesting entries found:**
  - 3 axioms: `propext`, `Classical.choice`, `Quot.sound` (the standard three)
  - 6 opaques: `IO.getStdin`, `IO.getStdout`, `IO.RealWorld.nonemptyType`, `Void.nonemptyType`, `String.Internal.append`, `Lean.opaqueId`
  - 82 externs: full FFI surface — `String.push` → `lean_string_push`, `panicCore` → `lean_panic_fn`, all `Nat.*`/`Int.*`/`UInt8.*`/`UInt32.*` arithmetic mapped to C symbols

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
    Audit.lean                # core auditor implementation
  Main.lean                   # experiment: #eval audit of myMain
  Explore.lean                # scratch file for API exploration (can delete)
```

---

## Design: Core Auditor

### Traversal

Walk `Expr` recursively. At every `Expr.const name levels`:
1. Skip if already in visited set (cycle detection)
2. Look up `name` in `Environment` via `env.find?`
3. Classify via `classifyConst` (axiom/opaque/extern or uninteresting)
4. If `shouldReport name`, add to entries
5. If `shouldRecurse name`, recurse into `ci.type` and `ci.value?`

All other `Expr` constructors (app, lam, forallE, letE, mdata, proj) recurse into subexpressions. Leaf nodes (bvar, fvar, mvar, sort, lit) stop.

### Configuration

Both predicates are caller-supplied:
- `shouldRecurse : Name → Bool` — controls traversal boundary
- `shouldReport : Name → Bool` — controls output filtering

These are independent. You can recurse into everything but only report externs, or recurse only into your own code but report axioms from the trusted boundary.

---

## Next Steps

### 1. Add expression path tracking ("cursor")

Currently we record *what* was found but not *where* in the expression tree it was found. Add a path/cursor that records the traversal route from the root expression to each finding.

Proposed data type:

```lean
inductive ExprStep where
  | appFn | appArg
  | lamType | lamBody
  | forallType | forallBody
  | letType | letVal | letBody
  | mdata | proj
  | constDef (name : Name)    -- entered the value of a looked-up constant
  | constType (name : Name)   -- entered the type of a looked-up constant

abbrev ExprPath := Array ExprStep
```

Each `AuditEntry` would carry an `ExprPath` showing how we got there.

### 2. Record the constant's instantiated type at usage site

When we hit `.const name levels`, the constant has universe parameters that get instantiated with `levels`. Record the instantiated type alongside the finding. This is pure (no MetaM needed) — just `ci.type.instantiateLevelParams ci.levelParams levels`.

This tells us "this extern is being used as `Nat → Nat → Nat`" rather than just "this extern exists."

### 3. (Harder) Record the expected type at the usage site

What does the surrounding context expect at that position? This requires either:
- Running in `MetaM` and calling `inferType` on the subexpression, or
- Manually threading a local context through binders (lambdas/foralls/lets)

This would tell us "at this app argument, Lean expects a `Nat`, and `Nat.add` is providing `Nat → Nat → Nat`."

### 4. Pretty-print grouped output

Group findings by category (axioms, opaques, externs) with their paths and types. Something like:

```
Audit of `myMain`:
  Axioms:
    propext       [constDef myMain → ... → constDef Decidable.em → constType ...]
    Classical.choice  [...]

  Opaques:
    IO.getStdin : BaseIO IO.FS.Stream  [constDef myMain → appArg → ...]

  Externs:
    String.push → lean_string_push : String → Char → String  [constDef myMain → ...]
```

### 5. Expose as `#audit` command

Create a command elaborator so users can write `#audit myMain` or `#audit myMain (trust := [Init, Std])`.

### 6. Extern symbol tracing (stretch)

For each extern symbol found, trace it back to the linked native library:
- Parse `lakefile.toml` for `moreLinkArgs`
- Find the `.a`/`.so` containing the symbol via `nm`/`objdump`
- Optionally find C source in the workspace

### 7. Admissibility proof (stretch)

Prove that `shouldReport name = true ∧ classifyConst env ci = some f → entry ∈ result.entries`. Should be straightforward from construction but would be a nice self-referential demonstration.

---

## Key Files to Read

- **`MyLeanTermAuditor/Audit.lean`** — all the auditor logic
- **`Main.lean`** — the working experiment (look at the `#eval` block)
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
