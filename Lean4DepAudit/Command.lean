import Lean
import Lean4DepAudit.Types
import Lean4DepAudit.Filter
import Lean4DepAudit.Monad

open Lean Elab Command Meta

namespace Lean4DepAudit

-- ============================================================================
-- Syntax
-- ============================================================================

/-- Audit one or more constants for axioms, opaques, and externs.

    ```
    #audit myMain
    #audit myMain with AuditConfig.runtimeExterns
    #audit (myMain, myOtherMain)
    #audit myMain with { drill := [`propext] }
    #audit myMain with { shouldReport := Filter.externsOnly }
    ```

    Without `with`, uses `AuditConfig.standard` (all axioms + runtime externs).
    The `with` clause accepts any expression of type `AuditConfig`. -/
syntax (name := auditSingle) "#audit" ident ("with" term)? : command
syntax (name := auditMulti) "#audit" "(" ident,+ ")" ("with" term)? : command

-- ============================================================================
-- Output formatting
-- ============================================================================

/-- Format a single finding line for display. -/
private def formatFinding (fi : FindingInfo) : MessageData :=
  let tag := match fi.finding with
    | .axiom_      => "axiom"
    | .opaque_ k   => s!"opaque ({k})"
    | .extern_ sym => s!"extern \"{sym}\""
  let rt := if fi.reachableAtRuntime then " [runtime]" else ""
  let kt := if fi.reachableInProof then " [kernel-time]" else ""
  let typeStr := if fi.typeStr.isEmpty then "" else s!" : {fi.typeStr}"
  m!"  {fi.name} [{tag}]{rt}{kt}{typeStr}  ({fi.location})  [{fi.numEncounters} encounters]"

/-- Format a section (e.g. "Axioms") with its findings. -/
private def formatSection (label : String) (findings : Array FindingInfo) : Array MessageData :=
  if findings.isEmpty then #[]
  else
    let header := m!"\n{label} ({findings.size}):"
    let lines := findings.map fun fi => m!"\n{formatFinding fi}"
    #[header] ++ lines

/-- Format the full audit summary as MessageData. -/
private def formatAuditSummary (result : AuditResult) (names : Array Name) : MessageData :=
  let all := result.findingsArray
  let axioms  := all.filter fun fi => fi.finding == .axiom_
  let opaques := all.filter fun fi => match fi.finding with | .opaque_ _ => true | _ => false
  let externs := all.filter fun fi => match fi.finding with | .extern_ _ => true | _ => false
  let header := m!"Audited {names.toList} — visited {result.numVisited} constants, \
    found {all.size} findings ({axioms.size} axioms, {opaques.size} opaques, {externs.size} externs)."
  let parts := #[header]
    ++ formatSection "Axioms" axioms
    ++ formatSection "Opaques" opaques
    ++ formatSection "Externs" externs
  MessageData.joinSep parts.toList ""

/-- Format a drill result as MessageData. -/
private def formatDrill (dr : DrillResult) : MessageData :=
  if dr.children.isEmpty then
    m!"  {dr.from_} does not reach {dr.target}"
  else
    let lines := dr.children.map fun child => m!"\n    {child}"
    m!"  {dr.from_} reaches {dr.target} through {dr.children.length} direct dep(s):" ++
      MessageData.joinSep lines ""

-- ============================================================================
-- Elaborator core
-- ============================================================================

/-- Extract names from the stx depending on the syntax kind. -/
private def extractNames (stx : Syntax) : CommandElabM (Array Name) := do
  let env ← getEnv
  if stx.getKind == ``auditSingle then
    -- stx[1] = ident
    let name := stx[1].getId
    unless env.find? name |>.isSome do
      throwErrorAt stx[1] m!"unknown constant '{name}'"
    return #[name]
  else
    -- stx[2] = null node with ident,+ children (idents interleaved with commas)
    let sepChildren := stx[2].getArgs
    let idents := sepChildren.filter (·.getKind == `ident)
    idents.mapM fun id => do
      let name := id.getId
      unless env.find? name |>.isSome do
        throwErrorAt id m!"unknown constant '{name}'"
      return name

/-- Extract the optional config term.
    - auditSingle: stx[2] = optional("with" term)
    - auditMulti:  stx[4] = optional("with" term) -/
private def extractConfigStx (stx : Syntax) : Option Syntax :=
  let opt := if stx.getKind == ``auditSingle then stx[2] else stx[4]
  if opt.isNone then none else some opt[1]

/-- Evaluate an AuditConfig from syntax, or return the standard default. -/
private unsafe def evalConfig (cfgStx? : Option Syntax) : CommandElabM AuditConfig :=
  match cfgStx? with
  | none => pure AuditConfig.standard
  | some cfgStx => liftTermElabM do
    let e ← Term.elabTerm cfgStx (some (mkConst ``AuditConfig))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    Meta.evalExpr AuditConfig (mkConst ``AuditConfig) e

/-- Run the full audit pipeline: pass 1 + resolve locations + optional drill. -/
private unsafe def runAudit (stx : Syntax) : CommandElabM Unit := do
  let names ← extractNames stx
  let config ← evalConfig (extractConfigStx stx)

  -- Pass 1: classification + DAG
  let result ← liftTermElabM <| Meta.MetaM.run' do
    AuditM.exec do
      auditConstsM config names
      resolveLocationsM

  -- Display summary
  logInfo (formatAuditSummary result names)

  -- Pass 2: drill-down (if targets specified in config)
  if !config.drill.isEmpty then
    let env ← getEnv
    for target in config.drill do
      let dr := drillDown env names[0]! target result
      logInfo m!"Drill: {formatDrill dr}"

-- ============================================================================
-- Register elaborators
-- ============================================================================

@[command_elab auditSingle]
unsafe def elabAuditSingle : CommandElab := runAudit

@[command_elab auditMulti]
unsafe def elabAuditMulti : CommandElab := runAudit

end Lean4DepAudit
