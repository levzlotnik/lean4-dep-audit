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

-- ---------- Type mismatch fixtures ----------

/-- Lean says UInt32 → UInt32, C returns uint8_t. Return type mismatch. -/
@[extern "test_ffi_wrong_ret"]
opaque ffiWrongRet : UInt32 → UInt32

/-- Lean says UInt32 → UInt32 → UInt32, C takes (uint32_t, uint8_t). Param type mismatch. -/
@[extern "test_ffi_wrong_param"]
opaque ffiWrongParam : UInt32 → UInt32 → UInt32

/-- Lean says UInt32 → UInt32, C takes two params. Arity mismatch. -/
@[extern "test_ffi_wrong_arity"]
opaque ffiWrongArity : UInt32 → UInt32

/-- Caller that reaches all three mismatched externs. -/
def callsMismatchedFfi (x y : UInt32) : UInt32 :=
  ffiWrongRet x + ffiWrongParam x y + ffiWrongArity x

end FfiFixture
