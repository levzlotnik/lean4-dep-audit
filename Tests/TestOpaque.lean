import Tests.Helpers

open Lean Lean4DepAudit

-- Test 1: Partial def found through caller (classified + transitively reached)
run_cmd runTest "Opaque: testCallsPartial finds testPartialFn as opaque_ .partial_" do
  let result ← runAudit `TestFixtures.Opaque.testCallsPartial
  assertHasFinding result `TestFixtures.Opaque.testPartialFn "Opaque Test 1a: "
  assertFindingIs result `TestFixtures.Opaque.testPartialFn (.opaque_ .partial_) "Opaque Test 1b: "

-- Test 2: Plain opaque found through caller (classified as implementedBy_)
run_cmd runTest "Opaque: testCallsOpaque finds testPlainOpaque as opaque_ .implementedBy_" do
  let result ← runAudit `TestFixtures.Opaque.testCallsOpaque
  assertHasFinding result `TestFixtures.Opaque.testPlainOpaque "Opaque Test 2a: "
  assertFindingIs result `TestFixtures.Opaque.testPlainOpaque
    (.opaque_ .implementedBy_) "Opaque Test 2b: "

-- Test 3: Standard config reports non-standard opaques
run_cmd runTest "Opaque: standard config reports user-code partial def" do
  let result ← runAudit `TestFixtures.Opaque.testCallsPartial AuditConfig.standard
  assertHasFinding result `TestFixtures.Opaque.testPartialFn "Opaque Test 3: "
