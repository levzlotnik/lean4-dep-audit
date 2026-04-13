import Tests.Helpers
import FfiFixture

open Lean Elab Command Meta MyLeanTermAuditor

-- ============================================================================
-- Provenance tests: verify each SymbolProvenance constructor
-- ============================================================================

-- tracedToSource: FfiFixture.ffiAdd has full trace chain to c/ffi.c
run_cmd runTest "Provenance: ffiAdd traced to ffi.c source" do
  let result ← runAuditWithProvenance `FfiFixture.callsFfiAdd AuditConfig.default
  assertHasFinding result `FfiFixture.ffiAdd
  assertTracedToSource result `FfiFixture.ffiAdd "ffi.c"

-- toolchainRuntime: a stdlib extern found in libleanrt.a
-- We audit String.append which transitively reaches ByteArray.mk (lean_byte_array_mk)
run_cmd runTest "Provenance: stdlib extern is toolchainRuntime" do
  let result ← runAuditWithProvenance `String.append AuditConfig.default
  -- Find any extern finding with toolchainRuntime provenance
  let findings := result.findingsArray
  let hasRuntime := findings.any fun fi =>
    match fi.finding, fi.provenance? with
    | .extern_ _, some (.toolchainRuntime _) => true
    | _, _ => false
  unless hasRuntime do
    throwError "Expected at least one finding with toolchainRuntime provenance"

-- toolchainHeader: a stdlib extern that is static inline in lean.h
-- Same audit of String.append reaches lean_uint32_to_nat (UInt32.toBitVec)
run_cmd runTest "Provenance: header-only extern is toolchainHeader" do
  let result ← runAuditWithProvenance `String.append AuditConfig.default
  let findings := result.findingsArray
  let hasHeader := findings.any fun fi =>
    match fi.finding, fi.provenance? with
    | .extern_ _, some .toolchainHeader => true
    | _, _ => false
  unless hasHeader do
    throwError "Expected at least one finding with toolchainHeader provenance"

-- unresolved: TestFixtures.Extern.testExternFn has no backing native code
run_cmd runTest "Provenance: unlinked extern is unresolved" do
  let result ← runAuditWithProvenance `TestFixtures.Extern.testCallsExtern AuditConfig.default
  assertHasFinding result `TestFixtures.Extern.testExternFn
  assertUnresolved result `TestFixtures.Extern.testExternFn
