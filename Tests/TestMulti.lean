import Tests.Helpers

open Lean Lean4DepAudit

-- Test 1: Multi-constant audit shares visited set
run_cmd runTest "Multi: shared AuditResult deduplicates findings" do
  let result ← runAuditMulti #[`TestFixtures.Chain.chainRoot, `TestFixtures.Chain.chainBranch]
  assertHasFinding result `TestFixtures.Chain.chainExtern "Multi Test 1a: "
  assertFindingIs result `TestFixtures.Chain.chainExtern
    (.extern_ "chain_leaf_extern") "Multi Test 1b: "

-- Test 2: Multi-constant with disjoint dependency trees
run_cmd runTest "Multi: disjoint trees still find expected findings" do
  let result ← runAuditMulti
    #[`TestFixtures.Chain.chainRoot, `TestFixtures.PureStdlib.testPureArith]
  assertHasFinding result `TestFixtures.Chain.chainExtern "Multi Test 2: "

-- Test 3: Multi-constant visits more constants than either alone
run_cmd runTest "Multi: combined audit visits >= each individual audit" do
  let r1 ← runAudit `TestFixtures.Chain.chainRoot
  let r2 ← runAudit `TestFixtures.PureStdlib.testPureArith
  let rBoth ← runAuditMulti
    #[`TestFixtures.Chain.chainRoot, `TestFixtures.PureStdlib.testPureArith]
  let nBoth := AuditResult.numVisited rBoth
  let n1 := AuditResult.numVisited r1
  let n2 := AuditResult.numVisited r2
  unless nBoth ≥ n1 do
    throwError "Multi Test 3a: Combined visited ({nBoth}) < chainRoot alone ({n1})"
  unless nBoth ≥ n2 do
    throwError "Multi Test 3b: Combined visited ({nBoth}) < testPureArith alone ({n2})"
