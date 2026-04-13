import Tests.Helpers
import FfiFixture

open Lean Lean4DepAudit

/-! # FFI tests

These tests audit constants from the `FfiFixture` package — a real Lake package
with C source compiled via `extern_lib`. The extern symbols (`test_ffi_add`, etc.)
are backed by actual linked native code in `libffi.a`, not just unresolved opaques.

This exercises the auditor's core value proposition: detecting trust boundaries
at the FFI/native-code boundary in real projects.
-/

-- Test 1: Direct FFI extern found when auditing its caller (classified + transitively reached)
run_cmd runTest "Ffi: callsFfiAdd finds ffiAdd as extern_ test_ffi_add" do
  let result ← runAudit `FfiFixture.callsFfiAdd
  assertHasFinding result `FfiFixture.ffiAdd "Ffi Test 1a: "
  assertFindingIs result `FfiFixture.ffiAdd (.extern_ "test_ffi_add") "Ffi Test 1b: "
  -- The caller itself should NOT be a finding (it's a plain def)
  assertNoFinding result `FfiFixture.callsFfiAdd "Ffi Test 1c: "

-- Test 2: Transitive detection — calling a function that calls an FFI extern
run_cmd runTest "Ffi: callsFfiAdd transitively finds ffiAdd" do
  let result ← runAudit `FfiFixture.callsFfiAdd
  assertHasFinding result `FfiFixture.ffiAdd "Ffi Test 2a: "
  assertFindingIs result `FfiFixture.ffiAdd (.extern_ "test_ffi_add") "Ffi Test 2b: "

-- Test 3: Multiple FFI externs from a single root
run_cmd runTest "Ffi: callsBothFfi finds both ffiAdd and ffiToggle" do
  let result ← runAudit `FfiFixture.callsBothFfi
  assertHasFinding result `FfiFixture.ffiAdd "Ffi Test 3a: "
  assertFindingIs result `FfiFixture.ffiAdd (.extern_ "test_ffi_add") "Ffi Test 3b: "
  assertHasFinding result `FfiFixture.ffiToggle "Ffi Test 3c: "
  assertFindingIs result `FfiFixture.ffiToggle (.extern_ "test_ffi_toggle") "Ffi Test 3d: "

-- Test 4: Chain drill-down through FFI dependency
run_cmd runTest "Ffi: drill from ffiChainRoot to ffiAdd finds callsFfiAdd" do
  let env ← getEnv
  let result ← runAudit `FfiFixture.ffiChainRoot
  assertHasFinding result `FfiFixture.ffiAdd "Ffi Test 4a: "
  assertHasFinding result `FfiFixture.ffiConst42 "Ffi Test 4b: "
  let dr := drillDown env `FfiFixture.ffiChainRoot `FfiFixture.ffiAdd result
  assertDrillContains dr `FfiFixture.callsFfiAdd "Ffi Test 4c: "

-- Test 5: FFI externs from external package are non-standard (standard config reports them)
run_cmd runTest "Ffi: standard config reports FfiFixture externs as non-standard" do
  let result ← runAudit `FfiFixture.callsFfiAdd AuditConfig.standard
  assertHasFinding result `FfiFixture.ffiAdd "Ffi Test 5: "

-- Test 6: Reachability flags for FFI externs
run_cmd runTest "Ffi: ffiAdd reachable at runtime, not in proof" do
  let result ← runAudit `FfiFixture.callsFfiAdd
  assertReachability result `FfiFixture.ffiAdd
    (runtime := true) (proof := false) "Ffi Test 6: "

-- Test 7: ffiConst42 (thunk pattern) detected with correct symbol
run_cmd runTest "Ffi: ffiConst42 detected as extern_ test_ffi_const42" do
  let result ← runAudit `FfiFixture.ffiChainRoot
  assertFindingIs result `FfiFixture.ffiConst42 (.extern_ "test_ffi_const42") "Ffi Test 7: "
