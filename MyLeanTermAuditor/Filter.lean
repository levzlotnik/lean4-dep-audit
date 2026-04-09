import Lean
import MyLeanTermAuditor.Types
import MyLeanTermAuditor.StackTrace

open Lean

namespace MyLeanTermAuditor

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

/-- Filter: only opaques. -/
def opaquesOnly : ConstContext → Bool :=
  fun ctx => ctx.finding == some Finding.opaque_

/-- Filter: only externs. -/
def externsOnly : ConstContext → Bool :=
  fun ctx => match ctx.finding with | some (Finding.extern_ _) => true | _ => false

/-- Filter: only findings reachable through runtime code (not proof terms).
    These are the externs/axioms your compiled binary actually depends on. -/
def runtimeOnly : ConstContext → Bool :=
  fun ctx => !ctx.inProofTerm

/-- Filter: only findings reachable through proof terms (kernel-time dependencies).
    These are externs/axioms the kernel evaluates during type-checking. -/
def kernelOnly : ConstContext → Bool :=
  fun ctx => ctx.inProofTerm

/-- Filter: constant chain depth (number of constDef/constType frames) ≤ n. -/
def maxDepth (n : Nat) : ConstContext → Bool :=
  fun ctx =>
    let depth := ctx.path.foldl (init := 0) fun acc step =>
      match step.constName? with | some _ => acc + 1 | none => acc
    depth ≤ n

/-- Filter: the path passes through a specific constant. -/
def pathThrough (target : Name) : ConstContext → Bool :=
  fun ctx => ctx.path.any fun step =>
    match step.constName? with
    | some (n, _) => n == target
    | none => false

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

end MyLeanTermAuditor
