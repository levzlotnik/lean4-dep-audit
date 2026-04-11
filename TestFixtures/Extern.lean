import Lean

namespace TestFixtures.Extern

/-- A custom extern binding — should be detected as `extern_ "test_c_fn"`. -/
@[extern "test_c_fn"] opaque testExternFn : Nat → Nat

/-- A function that calls the extern — auditing this should find `testExternFn`. -/
def testCallsExtern : Nat := testExternFn 42

/-- A second extern with a different symbol name. -/
@[extern "test_c_fn_2"] opaque testExternFn2 : String → String

/-- Calls both externs. -/
def testCallsBothExterns : Nat × String :=
  (testExternFn 1, testExternFn2 "hello")

end TestFixtures.Extern
