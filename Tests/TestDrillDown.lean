import Tests.Helpers

open Lean Lean4DepAudit

-- Test 1: Drill from chainRoot to chainExtern finds chainMiddle
run_cmd runTest "DrillDown: chainRoot -> chainExtern shows chainMiddle" do
  let env ← getEnv
  let result ← runAudit `TestFixtures.Chain.chainRoot
  let dr := drillDown env `TestFixtures.Chain.chainRoot `TestFixtures.Chain.chainExtern result
  assertDrillContains dr `TestFixtures.Chain.chainMiddle "DrillDown Test 1: "

-- Test 2: Drill from chainMultiPath to chainExtern finds both paths
run_cmd runTest "DrillDown: chainMultiPath -> chainExtern shows both branches" do
  let env ← getEnv
  let result ← runAudit `TestFixtures.Chain.chainMultiPath
  let dr := drillDown env `TestFixtures.Chain.chainMultiPath `TestFixtures.Chain.chainExtern result
  assertDrillContains dr `TestFixtures.Chain.chainMiddle "DrillDown Test 2a: "
  assertDrillContains dr `TestFixtures.Chain.chainBranch "DrillDown Test 2b: "

-- Test 3: Drill for non-existent target returns empty children
run_cmd runTest "DrillDown: non-existent target returns 0 children" do
  let env ← getEnv
  let result ← runAudit `TestFixtures.Chain.chainRoot
  let dr := drillDown env `TestFixtures.Chain.chainRoot `nonExistentConstant result
  assertDrillNumChildren dr 0 "DrillDown Test 3: "

-- Test 4: chainExtern appears in findings
run_cmd runTest "DrillDown: chainExtern detected as extern finding" do
  let result ← runAudit `TestFixtures.Chain.chainRoot
  assertHasFinding result `TestFixtures.Chain.chainExtern "DrillDown Test 4a: "
  assertFindingIs result `TestFixtures.Chain.chainExtern
    (.extern_ "chain_leaf_extern") "DrillDown Test 4b: "
