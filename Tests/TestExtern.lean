import Tests.Helpers

open Lean Lean4DepAudit

-- Test 1: Extern found when auditing caller (classified + transitively reached)
run_cmd runTest "Extern: testCallsExtern finds testExternFn as extern_" do
  let result ← runAudit `TestFixtures.Extern.testCallsExtern
  assertHasFinding result `TestFixtures.Extern.testExternFn "Test 1a: "
  assertFindingIs result `TestFixtures.Extern.testExternFn (.extern_ "test_c_fn") "Test 1b: "

-- Test 3: Multiple externs from single root
run_cmd runTest "Extern: testCallsBothExterns finds both extern symbols" do
  let result ← runAudit `TestFixtures.Extern.testCallsBothExterns
  assertHasFinding result `TestFixtures.Extern.testExternFn "Test 3a: "
  assertFindingIs result `TestFixtures.Extern.testExternFn (.extern_ "test_c_fn") "Test 3b: "
  assertHasFinding result `TestFixtures.Extern.testExternFn2 "Test 3c: "
  assertFindingIs result `TestFixtures.Extern.testExternFn2 (.extern_ "test_c_fn_2") "Test 3d: "

-- Test 4: Extern detected by standard config (user code, not stdlib)
run_cmd runTest "Extern: standard config reports non-standard externs" do
  let result ← runAudit `TestFixtures.Extern.testCallsExtern AuditConfig.standard
  assertHasFinding result `TestFixtures.Extern.testExternFn "Test 4: "

-- Test 5: Extern reachable at runtime (not in proof)
run_cmd runTest "Extern: reachableAtRuntime = true for runtime extern" do
  let result ← runAudit `TestFixtures.Extern.testCallsExtern
  assertReachability result `TestFixtures.Extern.testExternFn
    (runtime := true) (proof := false) "Test 5: "
