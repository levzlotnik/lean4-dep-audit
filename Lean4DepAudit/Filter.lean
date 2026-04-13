import Lean
import Lean4DepAudit.Types
import Lean4DepAudit.StackTrace

open Lean

namespace Lean4DepAudit

namespace Filter

/-- Filter by constant name. -/
def byName (p : Name → Bool) : ConstContext → Bool :=
  fun ctx => p ctx.name

/-- Filter: constant is in one of the given namespaces. -/
def inNamespaces (ns : List Name) : ConstContext → Bool :=
  fun ctx => ns.any (Name.isPrefixOf · ctx.name)

/-- Filter: constant is NOT in any of the given namespaces. -/
def notInNamespaces (ns : List Name) : ConstContext → Bool :=
  fun ctx => !ns.any (Name.isPrefixOf · ctx.name)

/-- Filter: only axioms. -/
def axiomsOnly : ConstContext → Bool :=
  fun ctx => ctx.finding == some Finding.axiom_

/-- Filter: only opaques (any kind). -/
def opaquesOnly : ConstContext → Bool :=
  fun ctx => match ctx.finding with | some (Finding.opaque_ _) => true | _ => false

/-- Filter: only partial defs. -/
def partialsOnly : ConstContext → Bool :=
  fun ctx => ctx.finding == some (Finding.opaque_ .partial_)

/-- Filter: only initialize refs. -/
def initializeOnly : ConstContext → Bool :=
  fun ctx => ctx.finding == some (Finding.opaque_ .initialize_)

/-- Filter: only externs. -/
def externsOnly : ConstContext → Bool :=
  fun ctx => match ctx.finding with | some (Finding.extern_ _) => true | _ => false

/-- Filter: only findings reachable through runtime code (not proof terms). -/
def runtimeOnly : ConstContext → Bool :=
  fun ctx => !ctx.inProofTerm

/-- The three standard axioms: `propext`, `Quot.sound`, `Classical.choice`. -/
def isStandardAxiom (name : Name) : Bool :=
  name == `propext || name == `Quot.sound || name == `Classical.choice

/-- Trusted library module prefixes. Constants declared in modules starting
    with these prefixes are considered part of the platform. -/
def standardModulePrefixes : List Name := [`Init, `Lean, `Std, `Mathlib]

/-- Is this constant declared in a trusted standard library module?
    Checks the module where the constant is defined, not its name
    (e.g. `IO.getStdin` is in module `Init.System.IO`). -/
def isStandardLibrary (ctx : ConstContext) : Bool :=
  match ctx.env.getModuleIdxFor? ctx.name with
  | some idx =>
    let modName := ctx.env.header.modules[idx.toNat]!.module
    standardModulePrefixes.any (Name.isPrefixOf · modName)
  | none => false  -- not from an import = user code

/-- Filter: non-standard axioms only (excludes propext, Quot.sound, Classical.choice). -/
def nonStandardAxiomsOnly : ConstContext → Bool :=
  fun ctx => Filter.axiomsOnly ctx && !isStandardAxiom ctx.name

/-- Filter: non-standard externs only (excludes Init, Lean, Std, Mathlib). -/
def nonStandardExternsOnly : ConstContext → Bool :=
  fun ctx => Filter.externsOnly ctx && !isStandardLibrary ctx

/-- Filter: non-standard opaques only (excludes Init, Lean, Std, Mathlib). -/
def nonStandardOpaquesOnly : ConstContext → Bool :=
  fun ctx => Filter.opaquesOnly ctx && !isStandardLibrary ctx

/-- Filter: only findings reachable through proof terms (kernel-time dependencies).
    These are externs/axioms the kernel evaluates during type-checking. -/
def kernelOnly : ConstContext → Bool :=
  fun ctx => ctx.inProofTerm

/-- Filter: constant chain depth ≤ n. -/
def maxDepth (n : Nat) : ConstContext → Bool :=
  fun ctx => ctx.depth ≤ n

/-- Filter: the traversal stack passes through a specific constant. -/
def pathThrough (target : Name) : ConstContext → Bool :=
  fun ctx => ctx.constStack.any (· == target)

/-- Filter: has a finding (is interesting). Useful for `shouldReport` —
    even with the default, `shouldReport` only fires on classified constants,
    but this makes it explicit. -/
def hasAnyFinding : ConstContext → Bool :=
  fun ctx => ctx.finding.isSome

/-- Combinator: logical AND of two predicates. -/
def «and» (f g : ConstContext → Bool) : ConstContext → Bool :=
  fun ctx => f ctx && g ctx

/-- Combinator: logical OR of two predicates. -/
def «or» (f g : ConstContext → Bool) : ConstContext → Bool :=
  fun ctx => f ctx || g ctx

/-- Combinator: logical NOT of a predicate. -/
def «not» (f : ConstContext → Bool) : ConstContext → Bool :=
  fun ctx => !f ctx

end Filter

namespace Descend

/-- Descend: skip proof terms entirely. When we're inside a theorem's value,
    don't descend into any structural subexpressions.
    This prunes the entire Lean.Omega / proof-checking subtree. -/
def skipProofTerms : DescendContext → Bool :=
  fun ctx => !ctx.inProofTerm

/-- Descend: skip type positions (forallType, lamType, letType).
    Keeps only computational content — bodies and values. -/
def skipTypes : DescendContext → Bool :=
  fun ctx => match ctx.step with
    | .forallType | .lamType | .letType => false
    | _ => true

/-- Descend: go everywhere (default behavior). -/
def all : DescendContext → Bool :=
  fun _ => true

/-- Combinator: logical AND of two descent predicates. -/
def «and» (f g : DescendContext → Bool) : DescendContext → Bool :=
  fun ctx => f ctx && g ctx

/-- Combinator: logical OR of two descent predicates. -/
def «or» (f g : DescendContext → Bool) : DescendContext → Bool :=
  fun ctx => f ctx || g ctx

end Descend

-- ============================================================================
-- Convenience config constructors
-- ============================================================================

/-- Config that skips recursing into trusted namespaces but still reports
    interesting things found at the boundary. -/
def AuditConfig.trustPrefixes (prefixes : List Name) : AuditConfig where
  shouldRecurse := Filter.notInNamespaces prefixes
  shouldReport  := fun _ => true

/-- Config: only report runtime dependencies (skip proof-term findings). -/
def AuditConfig.runtimeOnly : AuditConfig where
  shouldReport  := Filter.runtimeOnly
  shouldDescend := Descend.skipProofTerms

/-- Config: only report externs reachable through runtime code. -/
def AuditConfig.runtimeExterns : AuditConfig where
  shouldReport  := Filter.and Filter.externsOnly Filter.runtimeOnly
  shouldDescend := Descend.skipProofTerms

/-- Config: only report axioms (full traversal including proofs). -/
def AuditConfig.axiomsOnly : AuditConfig where
  shouldReport := Filter.axiomsOnly

/-- Standard config for the `#audit` command.
    Reports runtime externs and non-standard axioms. Skips proof-term descent.

    - **Runtime externs**: what foreign code does my binary link?
    - **Non-standard axioms**: any `axiom` beyond `propext`, `Quot.sound`,
      `Classical.choice` — these indicate dismissed proof obligations.
    - Skips the standard three axioms (every Lean program uses them).
    - Skips proof-term descent (no Omega/decidability noise). -/
def AuditConfig.standard : AuditConfig where
  shouldRecurse := fun ctx => !Filter.isStandardLibrary ctx
  shouldReport := fun ctx =>
    -- Report non-standard axioms (custom axioms = red flag)
    Filter.nonStandardAxiomsOnly ctx
    -- Report non-standard opaques (partial defs, initialize refs, etc.)
    || Filter.nonStandardOpaquesOnly ctx
    -- Report non-standard externs reachable at runtime
    || (Filter.nonStandardExternsOnly ctx && Filter.runtimeOnly ctx)
  shouldDescend := Descend.skipProofTerms

end Lean4DepAudit
