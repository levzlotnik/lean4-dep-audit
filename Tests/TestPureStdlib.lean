import Tests.Helpers

open Lean MyLeanTermAuditor

-- Test 1: Pure arithmetic — 0 findings with standard config
run_cmd runTest "PureStdlib: pure arithmetic has 0 findings (standard)" do
  let result ← runAudit `TestFixtures.PureStdlib.testPureArith AuditConfig.standard
  assertNumFindings result 0 "PureStdlib Test 1: "

-- Test 2: Pure IO — 0 findings with standard config
run_cmd runTest "PureStdlib: IO.println has 0 findings (standard)" do
  let result ← runAudit `TestFixtures.PureStdlib.testPureIO AuditConfig.standard
  assertNumFindings result 0 "PureStdlib Test 2: "

-- Test 3: Pure list processing — 0 findings with standard config
run_cmd runTest "PureStdlib: List.map has 0 findings (standard)" do
  let result ← runAudit `TestFixtures.PureStdlib.testPureList AuditConfig.standard
  assertNumFindings result 0 "PureStdlib Test 3: "

-- Test 4: Full config DOES find stdlib externs/axioms
run_cmd runTest "PureStdlib: default config finds stdlib externs in IO code" do
  let result ← runAudit `TestFixtures.PureStdlib.testPureIO AuditConfig.default
  let n := result.numFindings
  unless n > 0 do
    throwError "PureStdlib Test 4: Expected >0 findings with default config on IO code, got 0"
