namespace TestFixtures.Axiom

/-- A custom axiom — should be detected as non-standard axiom. -/
axiom testAxiom : False

/-- A function that uses the custom axiom. -/
def testUsesAxiom : Nat := testAxiom.elim

/-- A theorem proved with sorry — `sorryAx` should appear as an axiom. -/
theorem testSorryThm : 1 + 1 = 3 := by sorry

/-- A function whose type depends on the sorry theorem. -/
def testUsesSorry : Nat :=
  -- Force a dependency on testSorryThm by using it in a proof-carrying term
  let _ := testSorryThm
  42

end TestFixtures.Axiom
