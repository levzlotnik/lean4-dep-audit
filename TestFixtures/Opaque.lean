namespace TestFixtures.Opaque

/-- A partial def — should be classified as `opaque_ .partial_`. -/
partial def testPartialFn : Nat → Nat
  | 0 => 0
  | n + 1 => testPartialFn n

/-- A plain opaque — value is `@default T inst`, classified as `opaque_ .implementedBy_`. -/
opaque testPlainOpaque : Nat → Nat

/-- A function that calls the partial def. -/
def testCallsPartial : Nat := testPartialFn 10

/-- A function that calls the plain opaque. -/
def testCallsOpaque : Nat := testPlainOpaque 10

end TestFixtures.Opaque
