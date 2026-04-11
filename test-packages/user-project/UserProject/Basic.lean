namespace UserProject

-- A user-defined extern: the auditor should flag this as non-standard.
@[extern "user_custom_ffi"]
opaque userExternFn : Nat -> Nat

-- A user-defined axiom: the auditor should flag this as non-standard.
axiom userAxiom : 1 + 1 = 2

-- Pure function, no externs or axioms.
def pureFunction : Nat := 42

-- Calls the extern transitively.
def callsExtern : Nat := userExternFn 7

-- Uses the axiom in a proof term.
theorem usesAxiom : 1 + 1 = 2 := userAxiom

-- IO action that calls the extern.
def userMain : IO Unit := do
  IO.println s!"Result: {callsExtern}"

end UserProject
