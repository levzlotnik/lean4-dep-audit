import Tests.Helpers
import FfiFixture

open Lean Elab Command Meta Lean4DepAudit

-- ============================================================================
-- C type compatibility tests: verify mismatch detection
-- ============================================================================

-- Test 1: Compatible types are reported as compatible
run_cmd runTest "TypeCheck: ffiAdd has compatible C types" do
  let result ← runAuditWithTypeCheck `FfiFixture.callsFfiAdd
  assertHasFinding result `FfiFixture.ffiAdd
  assertTypeCheckCompatible result `FfiFixture.ffiAdd

-- Test 2: Return type mismatch (Lean says UInt32, C returns uint8_t)
run_cmd runTest "TypeCheck: ffiWrongRet has return type mismatch" do
  let result ← runAuditWithTypeCheck `FfiFixture.callsMismatchedFfi
  assertHasFinding result `FfiFixture.ffiWrongRet
  assertTypeCheckMismatch result `FfiFixture.ffiWrongRet "return type"

-- Test 3: Parameter type mismatch (Lean says UInt32, C takes uint8_t at param 1)
run_cmd runTest "TypeCheck: ffiWrongParam has parameter type mismatch" do
  let result ← runAuditWithTypeCheck `FfiFixture.callsMismatchedFfi
  assertHasFinding result `FfiFixture.ffiWrongParam
  assertTypeCheckMismatch result `FfiFixture.ffiWrongParam "param 1"

-- Test 4: Parameter count mismatch (Lean says 1 param, C takes 2)
run_cmd runTest "TypeCheck: ffiWrongArity has arity mismatch" do
  let result ← runAuditWithTypeCheck `FfiFixture.callsMismatchedFfi
  assertHasFinding result `FfiFixture.ffiWrongArity
  assertTypeCheckMismatch result `FfiFixture.ffiWrongArity "parameter count"
