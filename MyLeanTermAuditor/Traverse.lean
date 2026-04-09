import Lean
import MyLeanTermAuditor.Types
import MyLeanTermAuditor.Classify

open Lean

namespace MyLeanTermAuditor

/-- Internal traversal state threaded through the recursive walk. -/
structure TraversalState where
  /-- The constant whose body we're currently inside (for DescendContext). -/
  currentConst? : Option (Name × ConstantInfo) := none
  /-- Are we inside a proof term (theorem value)? -/
  inProofTerm   : Bool := false
  deriving Inhabited

/-- Core auditor: walk an `Expr`, collect interesting constants.
    The `path` parameter tracks the traversal route from the root to each finding.
    The `ts` parameter carries traversal state (current constant, proof term flag). -/
partial def auditExpr (env : Environment) (config : AuditConfig) (e : Expr)
    (path : ExprPath) (ts : TraversalState) (state : AuditResult) : AuditResult :=
  go e path ts state
where
  /-- Try to descend into a subexpression, checking `shouldDescend` first. -/
  descend (e : Expr) (step : ExprStep) (path : ExprPath) (ts : TraversalState)
      (s : AuditResult) : AuditResult :=
    let dctx : DescendContext := {
      step          := step
      path          := path
      currentConst? := ts.currentConst?
      inProofTerm   := ts.inProofTerm
    }
    if config.shouldDescend dctx then
      go e (path.push step) ts s
    else s
  go (e : Expr) (path : ExprPath) (ts : TraversalState) (s : AuditResult) : AuditResult :=
    match e with
    | .const name levels =>
      if s.visited.contains name then s
      else
        let s := { s with visited := s.visited.insert name }
        match env.find? name with
        | some ci =>
          let finding := classifyConst env ci
          let cctx : ConstContext := {
            env, name, ci, path, levels, finding
            inProofTerm := ts.inProofTerm
          }
          -- Classify and maybe report
          let s := if config.shouldReport cctx then
            match finding with
            | some f =>
              let entry : AuditEntry := { name, finding := f, path, inProofTerm := ts.inProofTerm }
              { s with entries := s.entries.push entry }
            | none   => s
          else s
          -- Recurse into the constant's type and value if config allows
          if config.shouldRecurse cctx then
            -- Update traversal state: entering this constant
            let tsType : TraversalState := {
              currentConst? := some (name, ci)
              inProofTerm := ts.inProofTerm
            }
            let s := go ci.type (path.push (.constType name)) tsType s
            match ci.value? with
            | some v =>
              -- Entering a theorem's value flips inProofTerm to true
              let inProof := ts.inProofTerm || isTheorem ci
              let tsDef : TraversalState := {
                currentConst? := some (name, ci)
                inProofTerm := inProof
              }
              go v (path.push (.constDef name)) tsDef s
            | none   => s
          else s
        | none => s
    | .app fn arg =>
        let s := descend fn .appFn path ts s
        descend arg .appArg path ts s
    | .lam _ ty body _ =>
        let s := descend ty .lamType path ts s
        descend body .lamBody path ts s
    | .forallE _ ty body _ =>
        let s := descend ty .forallType path ts s
        descend body .forallBody path ts s
    | .letE _ ty val body _ =>
        let s := descend ty .letType path ts s
        let s := descend val .letVal path ts s
        descend body .letBody path ts s
    | .mdata _ expr => descend expr .mdata path ts s
    | .proj _ _ expr => descend expr .proj path ts s
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => s

/-- Run the auditor on a named constant from the environment. -/
def auditConst (env : Environment) (config : AuditConfig) (name : Name) : AuditResult :=
  let empty : AuditResult := { entries := #[], visited := {} }
  match env.find? name with
  | some ci =>
    let tsType : TraversalState := { currentConst? := some (name, ci) }
    let s := auditExpr env config ci.type #[.constType name] tsType empty
    match ci.value? with
    | some v =>
      let tsDef : TraversalState := {
        currentConst? := some (name, ci)
        inProofTerm := isTheorem ci
      }
      auditExpr env config v #[.constDef name] tsDef s
    | none   => s
  | none => empty

end MyLeanTermAuditor
