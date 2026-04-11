namespace TestFixtures.PureStdlib

/-- Pure arithmetic — no axioms, no externs, no opaques. -/
def testPureArith : Nat := 1 + 2 + 3

/-- Pure IO action using only stdlib. Standard config should report 0 findings. -/
def testPureIO : IO Unit := IO.println "hello world"

/-- List processing — purely functional, stdlib only. -/
def testPureList : List Nat := [1, 2, 3].map (· + 1)

end TestFixtures.PureStdlib
