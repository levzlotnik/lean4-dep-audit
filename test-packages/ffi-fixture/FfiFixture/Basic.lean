namespace FfiFixture

/-- Addition backed by real C code in `c/ffi.c`. -/
@[extern "test_ffi_add"]
opaque ffiAdd : UInt32 → UInt32 → UInt32

/-- Boolean negation backed by real C code. -/
@[extern "test_ffi_toggle"]
opaque ffiToggle : Bool → Bool

/-- A constant-returning extern (thunk pattern). -/
@[extern "test_ffi_const42"]
opaque ffiConst42 : Unit → UInt32

/-- Pure Lean caller of ffiAdd — should transitively depend on the extern. -/
def callsFfiAdd (x y : UInt32) : UInt32 := ffiAdd x y

/-- Calls two different FFI functions. -/
def callsBothFfi (x y : UInt32) (b : Bool) : UInt32 × Bool :=
  (ffiAdd x y, ffiToggle b)

/-- A chain: callsFfiAdd → ffiAdd. Useful for drill-down testing. -/
def ffiChainRoot : UInt32 := callsFfiAdd 10 20 + ffiConst42 ()

end FfiFixture
