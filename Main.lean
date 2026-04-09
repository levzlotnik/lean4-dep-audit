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

-- Run at elaboration time: audit `myMain` and print results.
-- We run the auditor in CommandElabM which has access to the environment.
#eval do
  let env ← Lean.MonadEnv.getEnv (m := Lean.Elab.Command.CommandElabM)
  let result := auditConst env AuditConfig.default `myMain
  Lean.logInfo m!"=== Audit of `myMain` ===\n\
    Visited {result.visited.size} constants total.\n\
    Found {result.entries.size} interesting entries:"
  -- Group by finding type
  let axioms := result.entries.filter (fun (e : AuditEntry) => e.finding == Finding.axiom_)
  let opaques := result.entries.filter (fun (e : AuditEntry) => e.finding == Finding.opaque_)
  let externs := result.entries.filter (fun (e : AuditEntry) =>
    match e.finding with | Finding.extern_ _ => true | _ => false)
  -- Axioms — full stack trace (few entries, most interesting)
  Lean.logInfo m!"  Axioms ({axioms.size}):"
  for entry in axioms do
    Lean.logInfo m!"    {entry.name} [axiom]\n{entry.path.toStackTrace entry.name}"
  -- Opaques — full stack trace
  Lean.logInfo m!"  Opaques ({opaques.size}):"
  for entry in opaques do
    Lean.logInfo m!"    {entry.name} [opaque]\n{entry.path.toStackTrace entry.name}"
  -- Externs — compact trace (82 entries, would be noisy with full traces)
  Lean.logInfo m!"  Externs ({externs.size}):"
  for entry in externs do
    let sym := match entry.finding with | Finding.extern_ s => s | _ => "?"
    Lean.logInfo m!"    {entry.name} → \"{sym}\"\n\
      {entry.path.toCompactTrace entry.name}"

def main : IO Unit :=
  IO.println "Run the #eval above at elaboration time to see audit results."
