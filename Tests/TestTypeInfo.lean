import Tests.Helpers

open Lean MyLeanTermAuditor

-- Test 1: Extern finding records its declared type
run_cmd runTest "TypeInfo: extern testExternFn has type Nat → Nat" do
  let result ← runAudit `TestFixtures.Extern.testCallsExtern
  assertHasType result `TestFixtures.Extern.testExternFn "Test 1a: "
  -- After resolveLocations, typeStr should be populated
  let result ← resolveLocations result
  assertTypeStrContains result `TestFixtures.Extern.testExternFn "Nat" "Test 1b: "

-- Test 2: Second extern has different type
run_cmd runTest "TypeInfo: extern testExternFn2 has type String → String" do
  let result ← runAudit `TestFixtures.Extern.testCallsBothExterns
  let result ← resolveLocations result
  assertTypeStrContains result `TestFixtures.Extern.testExternFn2 "String" "Test 2: "

-- Test 3: Axiom finding records its declared type
run_cmd runTest "TypeInfo: axiom testAxiom has type False" do
  let result ← runAudit `TestFixtures.Axiom.testUsesAxiom
  assertHasType result `TestFixtures.Axiom.testAxiom "Test 3a: "
  let result ← resolveLocations result
  assertTypeStrContains result `TestFixtures.Axiom.testAxiom "False" "Test 3b: "

-- Test 4: Opaque finding records its declared type
run_cmd runTest "TypeInfo: partial def testPartialFn has type Nat → Nat" do
  let result ← runAudit `TestFixtures.Opaque.testCallsPartial
  assertHasType result `TestFixtures.Opaque.testPartialFn "Test 4a: "
  let result ← resolveLocations result
  assertTypeStrContains result `TestFixtures.Opaque.testPartialFn "Nat" "Test 4b: "

-- Test 5: Plain opaque records its declared type
run_cmd runTest "TypeInfo: opaque testPlainOpaque has type Nat → Nat" do
  let result ← runAudit `TestFixtures.Opaque.testCallsOpaque
  assertHasType result `TestFixtures.Opaque.testPlainOpaque "Test 5a: "
  let result ← resolveLocations result
  assertTypeStrContains result `TestFixtures.Opaque.testPlainOpaque "Nat" "Test 5b: "
