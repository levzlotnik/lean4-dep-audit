import Lean
import MyLeanTermAuditor.Types
import MyLeanTermAuditor.Classify

open Lean

namespace MyLeanTermAuditor

/-- Internal traversal state threaded through the first pass. -/
structure TraversalState where
  /-- The constant whose body we're currently inside. -/
  currentConst? : Option (Name × ConstantInfo) := none
  /-- Are we inside a proof term (theorem value)? -/
  inProofTerm   : Bool := false
  /-- Number of constant boundaries crossed from the root. -/
  depth         : Nat := 0
  /-- Chain of constant names on the current stack (most recent last). -/
  constStack    : Array Name := #[]
  deriving Inhabited

/-- Record reverse dependency edges for a constant: for each `.const` in its
    type and value, add `child → parent` to the reverse dep graph.
    Uses `Expr.foldConsts` — a fast built-in scan. -/
def recordDepsFor (parent : Name) (ci : ConstantInfo) (s : AuditResult) : AuditResult :=
  let children : NameHashSet :=
    ci.type.foldConsts {} fun name (set : NameHashSet) => set.insert name
  let children : NameHashSet := match ci.value? with
    | some v => v.foldConsts children fun name (set : NameHashSet) => set.insert name
    | none   => children
  children.fold (init := s) fun s child =>
    let parents := match s.reverseDeps.find? child with
      | some set => set.insert parent
      | none     => ({} : NameHashSet).insert parent
    { s with reverseDeps := s.reverseDeps.insert child parents }

/-- First pass: walk an `Expr`, classify constants, build dep graph.
    Pure function — no MetaM, no paths, no local context. -/
partial def auditExpr (env : Environment) (config : AuditConfig) (e : Expr)
    (ts : TraversalState) (s : AuditResult) : AuditResult :=
  go e ts s
where
  descend (e : Expr) (step : ExprStep) (ts : TraversalState) (s : AuditResult) : AuditResult :=
    let dctx : DescendContext := {
      step          := step
      currentConst? := ts.currentConst?
      inProofTerm   := ts.inProofTerm
    }
    if config.shouldDescend dctx then go e ts s else s

  go (e : Expr) (ts : TraversalState) (s : AuditResult) : AuditResult :=
    match e with
    | .const name levels =>
      let bodyTraversed := s.visited.contains name
      match env.find? name with
      | some ci =>
        let finding := classifyConst env ci
        let cctx : ConstContext := {
          env, name, ci, levels, finding
          inProofTerm := ts.inProofTerm
          depth       := ts.depth
          constStack  := ts.constStack
        }
        -- Update finding info (flags only)
        let s := match finding with
          | some f =>
            if config.shouldReport cctx then
              match s.findings.find? name with
              | some fi =>
                let fi := { fi with
                  reachableAtRuntime := fi.reachableAtRuntime || !ts.inProofTerm
                  reachableInProof   := fi.reachableInProof || ts.inProofTerm
                  numEncounters      := fi.numEncounters + 1
                }
                { s with findings := s.findings.insert name fi }
              | none =>
                let fi : FindingInfo := {
                  name := name, finding := f
                  type := ci.type
                  location := { module := Name.anonymous }
                  reachableAtRuntime := !ts.inProofTerm
                  reachableInProof   := ts.inProofTerm
                  numEncounters      := 1
                }
                { s with findings := s.findings.insert name fi }
            else s
          | none => s
        -- Traverse body + record deps only on first encounter
        if !bodyTraversed then
          let s := { s with visited := s.visited.insert name }
          let s := recordDepsFor name ci s
          if config.shouldRecurse cctx then
            let tsChild : TraversalState := {
              currentConst? := some (name, ci)
              inProofTerm := ts.inProofTerm
              depth       := ts.depth + 1
              constStack  := ts.constStack.push name
            }
            let s := go ci.type tsChild s
            match ci.value? with
            | some v =>
              let tsChildDef := { tsChild with
                inProofTerm := ts.inProofTerm || isTheorem ci
              }
              go v tsChildDef s
            | none => s
          else s
        else s
      | none => s
    | .app fn arg =>
      let s := descend fn .appFn ts s
      descend arg .appArg ts s
    | .lam _ ty body _ =>
      let s := descend ty .lamType ts s
      descend body .lamBody ts s
    | .forallE _ ty body _ =>
      let s := descend ty .forallType ts s
      descend body .forallBody ts s
    | .letE _ ty val body _ =>
      let s := descend ty .letType ts s
      let s := descend val .letVal ts s
      descend body .letBody ts s
    | .mdata _ expr => descend expr .mdata ts s
    | .proj _ _ expr => descend expr .proj ts s
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => s

/-- Run the first audit pass on a named constant. Pure function.
    Pass a `prior` result to accumulate incrementally (e.g. for bulk audits). -/
def auditConst (env : Environment) (config : AuditConfig) (name : Name)
    (prior : AuditResult := {}) : AuditResult :=
  match env.find? name with
  | some ci =>
    let tsBase : TraversalState := {
      currentConst? := some (name, ci)
      constStack    := #[name]
      depth         := 1
    }
    let s := auditExpr env config ci.type tsBase prior
    match ci.value? with
    | some v =>
      let tsDef := { tsBase with inProofTerm := isTheorem ci }
      auditExpr env config v tsDef s
    | none => s
  | none => prior

/-- Fill in source locations for all findings. Requires MonadEnv + BaseIO.
    Call this once after auditConst to populate the location fields. -/
def resolveLocations (result : AuditResult) : MetaM AuditResult := do
  let env ← getEnv
  let findings ← result.findings.foldlM (init := result.findings) fun acc name fi => do
    let needsLocation := fi.location.module == Name.anonymous
    let needsTypeStr := fi.typeStr.isEmpty
    if needsLocation || needsTypeStr then
      let fi ← if needsLocation then do
        let module := match env.getModuleIdxFor? name with
          | some idx => env.header.modules[idx.toNat]!.module
          | none     => env.header.mainModule
        let range? ← do
          match ← findDeclarationRanges? name with
          | some ranges => pure (some ranges.range)
          | none        => pure none
        pure { fi with location := { module := module, range? := range? } }
      else pure fi
      let fi ← if needsTypeStr then do
        let fmt ← Meta.ppExpr fi.type
        pure { fi with typeStr := toString fmt }
      else pure fi
      return acc.insert name fi
    else
      return acc
  return { result with findings := findings }

-- ============================================================================
-- Second pass: targeted path collection
-- ============================================================================

/-- Find all ancestors of `target` in the reverse dep graph — constants that
    transitively reference `target`. Returns the set of ancestor names. -/
partial def findAncestors (result : AuditResult) (target : Name) : NameHashSet :=
  go #[target] {}
where
  go (queue : Array Name) (seen : NameHashSet) : NameHashSet :=
    if queue.isEmpty then seen
    else
      let (next, rest) := (queue.back!, queue.pop)
      if seen.contains next then go rest seen
      else
        let seen := seen.insert next
        match result.reverseDeps.find? next with
        | some parents =>
          let rest := parents.fold (init := rest) fun acc parent => acc.push parent
          go rest seen
        | none => go rest seen

/-- Get the immediate constant-level dependencies of a constant (from its type + value). -/
def immediateDeps (env : Environment) (name : Name) : NameHashSet :=
  match env.find? name with
  | some ci =>
    let deps : NameHashSet :=
      ci.type.foldConsts {} fun n (set : NameHashSet) => set.insert n
    match ci.value? with
    | some v => v.foldConsts deps fun n (set : NameHashSet) => set.insert n
    | none   => deps
  | none => {}

/-- Drill down one level: which direct dependencies of `from_` transitively reach `target`?
    Pure function — intersects immediate deps with the ancestor set of `target`. -/
def drillDown (env : Environment) (from_ target : Name) (result : AuditResult)
    : DrillResult :=
  let ancestors := findAncestors result target
  let deps := immediateDeps env from_
  let relevant := deps.fold (init := ([] : List Name)) fun acc child =>
    if ancestors.contains child then child :: acc else acc
  { from_ := from_, target := target, children := relevant }

end MyLeanTermAuditor
