import Lean4DepAudit

open Lean4DepAudit

/-- A sample function to audit — uses IO, string interpolation, etc. -/
def myMain : IO Unit := do
  let stdin ← IO.getStdin
  let name ← stdin.getLine
  IO.println s!"Hello, {name.trimAscii}!"

def main : IO Unit :=
  IO.println "Run `lake build` to see #audit results in the build output."

set_option profiler true

-- ============================================================================
-- Demo 1: Standard audit (all axioms + runtime externs)
-- ============================================================================
#audit myMain

-- ============================================================================
-- Demo 2: Runtime externs only
-- ============================================================================
#audit myMain with AuditConfig.runtimeExterns

-- ============================================================================
-- Demo 3: Full audit (everything — axioms, opaques, externs)
-- ============================================================================
#audit myMain with AuditConfig.default

-- ============================================================================
-- Demo 4: Drill-down — "why does myMain depend on propext?"
-- ============================================================================
#audit myMain with { drill := [`propext] }

-- ============================================================================
-- Demo 5: Multiple constants
-- ============================================================================
#audit (myMain, main)
