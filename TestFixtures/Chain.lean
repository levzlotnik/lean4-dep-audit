namespace TestFixtures.Chain

/-- Leaf extern — the target for drill-down queries. -/
@[extern "chain_leaf_extern"] opaque chainExtern : Nat → Nat

/-- Middle node — calls the extern. -/
def chainMiddle : Nat := chainExtern 1 + chainExtern 2

/-- Root node — calls the middle. Drill from here to `chainExtern`
    should show `chainMiddle` as an intermediary. -/
def chainRoot : Nat := chainMiddle + 100

/-- A second branch that also reaches the extern. -/
def chainBranch : Nat := chainExtern 99

/-- A root with two paths to the extern (through middle and branch). -/
def chainMultiPath : Nat := chainMiddle + chainBranch

end TestFixtures.Chain
