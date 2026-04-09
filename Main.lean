import MyLeanTermAuditor

open Lean MyLeanTermAuditor

/-- A sample function to audit — uses IO, string interpolation, etc. -/
def myMain : IO Unit := do
  let stdin ← IO.getStdin
  let name ← stdin.getLine
  IO.println s!"Hello, {name.trimAscii}!"

/-- Format a Finding for display. -/
def findingToString : Finding → String
  | .axiom_    => "axiom"
  | .opaque_   => "opaque"
  | .extern_ s => s!"extern \"{s}\""

/-- Helper: print a grouped audit result. -/
def printAuditResult (label : String) (result : AuditResult) : Lean.Elab.Command.CommandElabM Unit := do
  Lean.logInfo m!"=== {label} ===\n\
    Visited {result.visited.size} constants, found {result.entries.size} interesting entries."
  let axioms := result.entries.filter (fun (e : AuditEntry) => e.finding == Finding.axiom_)
  let opaques := result.entries.filter (fun (e : AuditEntry) => e.finding == Finding.opaque_)
  let externs := result.entries.filter (fun (e : AuditEntry) =>
    match e.finding with | Finding.extern_ _ => true | _ => false)
  if !axioms.isEmpty then
    Lean.logInfo m!"  Axioms ({axioms.size}):"
    for entry in axioms do
      let tag := if entry.inProofTerm then " [kernel-time]" else ""
      Lean.logInfo m!"    {entry.name} [axiom]{tag}\n{entry.path.toStackTrace entry.name}"
  if !opaques.isEmpty then
    Lean.logInfo m!"  Opaques ({opaques.size}):"
    for entry in opaques do
      let tag := if entry.inProofTerm then " [kernel-time]" else ""
      Lean.logInfo m!"    {entry.name} [opaque]{tag}\n{entry.path.toStackTrace entry.name}"
  if !externs.isEmpty then
    Lean.logInfo m!"  Externs ({externs.size}):"
    for entry in externs do
      let sym := match entry.finding with | Finding.extern_ s => s | _ => "?"
      let tag := if entry.inProofTerm then " [kernel-time]" else ""
      Lean.logInfo m!"    {entry.name} → \"{sym}\"{tag}\n\
        {entry.path.toCompactTrace entry.name}"

-- ============================================================================
-- Demo 1: Full audit (everything, no filtering)
-- ============================================================================
#eval do
  let env ← Lean.MonadEnv.getEnv (m := Lean.Elab.Command.CommandElabM)
  let result := auditConst env AuditConfig.default `myMain
  printAuditResult "Full audit of `myMain`" result

-- ============================================================================
-- Demo 2: Runtime-only externs (skip proof machinery)
-- ============================================================================
#eval do
  let env ← Lean.MonadEnv.getEnv (m := Lean.Elab.Command.CommandElabM)
  let result := auditConst env AuditConfig.runtimeExterns `myMain
  printAuditResult "Runtime externs of `myMain` (proof terms skipped)" result

-- ============================================================================
-- Demo 3: Runtime-only (all categories, proof terms skipped)
-- ============================================================================
#eval do
  let env ← Lean.MonadEnv.getEnv (m := Lean.Elab.Command.CommandElabM)
  let result := auditConst env AuditConfig.runtimeOnly `myMain
  printAuditResult "Runtime deps of `myMain` (proof terms skipped)" result

def main : IO Unit :=
  IO.println "Run the #eval blocks above at elaboration time to see audit results."
