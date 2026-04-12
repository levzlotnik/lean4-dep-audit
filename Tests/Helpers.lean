import MyLeanTermAuditor
import TestFixtures

open Lean Elab Command Meta MyLeanTermAuditor

/-- Assert that an `AuditResult` has exactly `n` findings. -/
def assertNumFindings (result : AuditResult) (expected : Nat) (ctx : String := "") : MetaM Unit := do
  let actual := result.numFindings
  unless actual == expected do
    throwError "{ctx}Expected {expected} finding(s), got {actual}"

/-- Assert that a constant is in the findings. -/
def assertHasFinding (result : AuditResult) (name : Name) (ctx : String := "") : MetaM Unit := do
  unless result.findings.find? name |>.isSome do
    throwError "{ctx}Expected '{name}' in findings, but it was not found"

/-- Assert that a constant is NOT in the findings. -/
def assertNoFinding (result : AuditResult) (name : Name) (ctx : String := "") : MetaM Unit := do
  if result.findings.find? name |>.isSome then
    throwError "{ctx}Expected '{name}' NOT in findings, but it was present"

/-- Assert the finding classification of a constant. -/
def assertFindingIs (result : AuditResult) (name : Name) (expected : Finding)
    (ctx : String := "") : MetaM Unit := do
  match result.findings.find? name with
  | some fi =>
    unless fi.finding == expected do
      throwError "{ctx}Expected finding for '{name}' to be {repr expected}, got {repr fi.finding}"
  | none => throwError "{ctx}Expected '{name}' in findings, but it was not found"

/-- Assert that a finding has the given reachability flags. -/
def assertReachability (result : AuditResult) (name : Name)
    (runtime : Bool) (proof : Bool) (ctx : String := "") : MetaM Unit := do
  match result.findings.find? name with
  | some fi =>
    unless fi.reachableAtRuntime == runtime do
      throwError "{ctx}Expected '{name}' reachableAtRuntime={runtime}, got {fi.reachableAtRuntime}"
    unless fi.reachableInProof == proof do
      throwError "{ctx}Expected '{name}' reachableInProof={proof}, got {fi.reachableInProof}"
  | none => throwError "{ctx}Expected '{name}' in findings, but it was not found"

/-- Assert that a drill result contains a specific child. -/
def assertDrillContains (dr : DrillResult) (child : Name) (ctx : String := "") : MetaM Unit := do
  unless dr.children.any (· == child) do
    throwError "{ctx}Expected drill from '{dr.from_}' to '{dr.target}' to contain '{child}', \
      got {dr.children.map Name.toString}"

/-- Assert that a drill result has exactly `n` children. -/
def assertDrillNumChildren (dr : DrillResult) (expected : Nat)
    (ctx : String := "") : MetaM Unit := do
  let actual := dr.children.length
  unless actual == expected do
    throwError "{ctx}Expected drill to have {expected} children, got {actual}: \
      {dr.children.map Name.toString}"

/-- Run audit on a constant with a given config and return the result. -/
def runAudit (name : Name) (config : AuditConfig := AuditConfig.default) : MetaM AuditResult := do
  let env ← getEnv
  return auditConst env config name

/-- Run audit on multiple constants with a shared result. -/
def runAuditMulti (names : Array Name) (config : AuditConfig := AuditConfig.default)
    : MetaM AuditResult := do
  let env ← getEnv
  let mut result : AuditResult := {}
  for name in names do
    result := auditConst env config name result
  return result

/-- Assert that a finding has a non-default type recorded. -/
def assertHasType (result : AuditResult) (name : Name) (ctx : String := "") : MetaM Unit := do
  match result.findings.find? name with
  | some fi =>
    -- The default is `.sort .zero`; any real type should differ
    if fi.type == .sort .zero then
      throwError "{ctx}Expected '{name}' to have a type recorded, but got default Sort 0"
  | none => throwError "{ctx}Expected '{name}' in findings, but it was not found"

/-- Assert that a finding's pretty-printed type string contains a substring. -/
def assertTypeStrContains (result : AuditResult) (name : Name) (substr : String)
    (ctx : String := "") : MetaM Unit := do
  match result.findings.find? name with
  | some fi =>
    unless fi.typeStr.hasSubstr substr do
      throwError "{ctx}Expected typeStr for '{name}' to contain \"{substr}\", got \"{fi.typeStr}\""
  | none => throwError "{ctx}Expected '{name}' in findings, but it was not found"

/-- Lift a MetaM test body into a `run_cmd`-compatible CommandElabM. -/
def runTest (name : String) (body : MetaM Unit) : CommandElabM Unit :=
  liftTermElabM <| Meta.MetaM.run' do
    body
    Lean.logInfo m!"PASS: {name}"
