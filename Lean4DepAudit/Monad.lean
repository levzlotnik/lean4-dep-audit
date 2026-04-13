import Lean
import Lean4DepAudit.Types
import Lean4DepAudit.Traverse

open Lean

namespace Lean4DepAudit

/-- Audit monad: threads `AuditResult` state through `MetaM`.
    Used by the orchestration layer that sequences multiple audits,
    resolves locations, and runs drill queries. -/
abbrev AuditM := StateT AuditResult MetaM

/-- Audit a single constant, accumulating into the shared state. -/
def auditConstM (config : AuditConfig) (name : Name) : AuditM Unit := do
  let env ← getEnv
  let prior ← get
  set (auditConst env config name prior)

/-- Audit multiple constants incrementally. Constants sharing dependencies
    are traversed only once thanks to the shared `visited` set. -/
def auditConstsM (config : AuditConfig) (names : Array Name) : AuditM Unit :=
  names.forM (auditConstM config)

/-- Fill in source locations for all findings in the current state. -/
def resolveLocationsM : AuditM Unit := do
  let result ← get
  let result ← resolveLocations result
  set result

/-- Run a drill-down query against the current audit state. -/
def drillDownM (from_ target : Name) : AuditM DrillResult := do
  let env ← getEnv
  let result ← get
  return drillDown env from_ target result

/-- Run an `AuditM` computation and return both the result and final state. -/
def AuditM.run' (m : AuditM α) : MetaM (α × AuditResult) :=
  StateT.run m {}

/-- Run an `AuditM` computation, discarding the value and returning the state. -/
def AuditM.exec (m : AuditM Unit) : MetaM AuditResult :=
  return (← StateT.run m {}).2

end Lean4DepAudit
