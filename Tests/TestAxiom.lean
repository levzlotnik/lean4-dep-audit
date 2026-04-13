import Tests.Helpers

open Lean Lean4DepAudit

-- Test 1: Custom axiom found through caller (classified + transitively reached)
run_cmd runTest "Axiom: testUsesAxiom finds testAxiom as axiom_" do
  let result ← runAudit `TestFixtures.Axiom.testUsesAxiom
  assertHasFinding result `TestFixtures.Axiom.testAxiom "Axiom Test 1a: "
  assertFindingIs result `TestFixtures.Axiom.testAxiom .axiom_ "Axiom Test 1b: "

-- Test 2: Custom axiom detected by standard config (non-standard)
run_cmd runTest "Axiom: standard config flags non-standard axiom" do
  let result ← runAudit `TestFixtures.Axiom.testUsesAxiom AuditConfig.standard
  assertHasFinding result `TestFixtures.Axiom.testAxiom "Axiom Test 2: "

-- Test 3: Sorry generates `sorryAx` — classified as extern_ "lean_sorry"
-- (sorryAx has @[extern "lean_sorry"], and extern classification takes priority)
run_cmd runTest "Axiom: sorry generates sorryAx (extern_ lean_sorry)" do
  let result ← runAudit `TestFixtures.Axiom.testSorryThm
  assertHasFinding result `sorryAx "Axiom Test 3a: "
  assertFindingIs result `sorryAx (.extern_ "lean_sorry") "Axiom Test 3b: "

-- Test 4: Sorry detected through transitive dependency
run_cmd runTest "Axiom: testUsesSorry finds sorryAx via testSorryThm" do
  let result ← runAudit `TestFixtures.Axiom.testUsesSorry
  assertHasFinding result `sorryAx "Axiom Test 4: "
