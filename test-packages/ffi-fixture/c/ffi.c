/**
 * FFI fixture: C implementations for test extern bindings.
 *
 * These functions back the @[extern] declarations in FfiFixture/Basic.lean.
 * They exist so the auditor can operate on constants that are backed by
 * real linked native code — not just opaque declarations with no library.
 */

#include <lean/lean.h>
#include <stdint.h>

/* test_ffi_add : UInt32 → UInt32 → UInt32 */
LEAN_EXPORT uint32_t test_ffi_add(uint32_t a, uint32_t b) {
    return a + b;
}

/* test_ffi_toggle : Bool → Bool
   Lean Bool is represented as uint8_t (0 = false, 1 = true). */
LEAN_EXPORT uint8_t test_ffi_toggle(uint8_t b) {
    return !b;
}

/* test_ffi_const42 : Unit → UInt32
   A thunk-style extern that takes no meaningful argument. */
LEAN_EXPORT uint32_t test_ffi_const42(lean_obj_arg unit) {
    return 42;
}
