-- Cross-project CLI integration tests for `lake exe audit`.
-- Tests run from test-packages/user-project/, which `require`s MyLeanTermAuditor,
-- simulating a real user's project. Invokes `lake exe MyLeanTermAuditor/audit`.
--
-- Run: `lake build audit && lake build test_cli && lake exe test_cli`

/-- Check if `haystack` contains `needle` as a substring. -/
def String.hasSubstr (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else
    let hLen := haystack.length
    let nLen := needle.length
    if nLen > hLen then false
    else Id.run do
      for i in List.range (hLen - nLen + 1) do
        if (haystack.drop i).startsWith needle then return true
      return false

structure TestCase where
  name : String
  args : Array String
  expectExit : UInt32 := 0
  expectStdout : Array String := #[]
  expectStderr : Array String := #[]
  rejectStdout : Array String := #[]

/-- The user project directory where we simulate a real user running the auditor. -/
def userProjectDir : String := "test-packages/user-project"

/-- Run `lake exe MyLeanTermAuditor/audit <args>` from the user project directory. -/
def runAudit (tc : TestCase) : IO Bool := do
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "MyLeanTermAuditor/audit"] ++ tc.args
    cwd := some userProjectDir
  }
  let mut passed := true
  if result.exitCode != tc.expectExit then
    IO.eprintln s!"FAIL [{tc.name}]: expected exit code {tc.expectExit}, got {result.exitCode}"
    IO.eprintln s!"  stdout: {result.stdout.take 300}"
    IO.eprintln s!"  stderr: {result.stderr.take 300}"
    passed := false
  for substr in tc.expectStdout do
    if !result.stdout.hasSubstr substr then
      IO.eprintln s!"FAIL [{tc.name}]: expected stdout to contain \"{substr}\""
      IO.eprintln s!"  stdout: {result.stdout.take 500}"
      passed := false
  for substr in tc.expectStderr do
    if !result.stderr.hasSubstr substr then
      IO.eprintln s!"FAIL [{tc.name}]: expected stderr to contain \"{substr}\""
      IO.eprintln s!"  stderr: {result.stderr.take 500}"
      passed := false
  for substr in tc.rejectStdout do
    if result.stdout.hasSubstr substr then
      IO.eprintln s!"FAIL [{tc.name}]: expected stdout NOT to contain \"{substr}\""
      passed := false
  if passed then
    IO.println s!"PASS: {tc.name}"
  return passed

def tests : Array TestCase := #[
  -- ========================================================================
  -- Basic CLI behavior (these don't need a real environment)
  -- ========================================================================

  { name := "help flag"
    args := #["--help"]
    expectStdout := #["Usage:", "--import", "--config", "Filter DSL:"] },

  { name := "no args error"
    args := #[]
    expectExit := 1
    expectStderr := #["no constants specified"] },

  { name := "no imports error"
    args := #["foo"]
    expectExit := 1
    expectStderr := #["no imports specified"] },

  { name := "bad config preset"
    args := #["foo", "--import", "UserProject", "--config", "bogus"]
    expectExit := 1
    expectStderr := #["unknown config preset"] },

  { name := "bad report atom"
    args := #["foo", "--import", "UserProject", "--report", "badAtom"]
    expectExit := 1
    expectStderr := #["unknown report atom"] },

  { name := "bad descend atom"
    args := #["foo", "--import", "UserProject", "--descend", "badAtom"]
    expectExit := 1
    expectStderr := #["unknown descend atom"] },

  { name := "unknown option"
    args := #["foo", "--import", "UserProject", "--bogus"]
    expectExit := 1
    expectStderr := #["unknown option"] },

  { name := "nonexistent constant"
    args := #["NoSuchConst", "--import", "UserProject"]
    expectStderr := #["not found in environment"]
    expectStdout := #["0 findings"] },

  -- ========================================================================
  -- Cross-project audits on UserProject constants
  -- ========================================================================

  -- Standard config: pure function → 0 findings
  { name := "user: pure function 0 findings"
    args := #["UserProject.pureFunction", "--import", "UserProject"]
    expectStdout := #["0 findings"] },

  -- Standard config: detects user's non-standard extern
  { name := "user: standard config finds extern"
    args := #["UserProject.callsExtern", "--import", "UserProject"]
    expectStdout := #["UserProject.userExternFn", "user_custom_ffi", "1 findings"] },

  -- Standard config: detects user's non-standard axiom
  { name := "user: standard config finds axiom"
    args := #["UserProject.usesAxiom", "--import", "UserProject"]
    expectStdout := #["UserProject.userAxiom", "axiom"] },

  -- Full config on IO action: more findings from stdlib
  { name := "user: full config on IO"
    args := #["UserProject.userMain", "--import", "UserProject", "--config", "full"]
    expectStdout := #["UserProject.userExternFn", "user_custom_ffi"] },

  -- Drill-down: userMain → callsExtern → userExternFn
  { name := "user: drill-down to extern"
    args := #["UserProject.userMain", "--import", "UserProject",
              "--config", "full", "--drill", "UserProject.userExternFn"]
    expectStdout := #["Drill-down:", "reaches UserProject.userExternFn",
                       "UserProject.callsExtern"] },

  -- Multiple constants from user project
  { name := "user: multi constant"
    args := #["UserProject.callsExtern", "UserProject.usesAxiom",
              "--import", "UserProject", "--config", "full"]
    expectStdout := #["user_custom_ffi", "UserProject.userAxiom"] },

  -- Filter DSL: externs only, no axioms in findings
  { name := "user: DSL externs only"
    args := #["UserProject.userMain", "--import", "UserProject",
              "--config", "full", "--report", "externs"]
    expectStdout := #["user_custom_ffi"]
    rejectStdout := #["Axioms ("] },

  -- Filter DSL: negation filters out stdlib
  { name := "user: DSL externs & !stdlib"
    args := #["UserProject.userMain", "--import", "UserProject",
              "--config", "full", "--report", "externs & !stdlib"]
    expectStdout := #["user_custom_ffi"]
    rejectStdout := #["lean_nat", "lean_string"] },

  -- Filter DSL: axioms only
  { name := "user: DSL axioms only"
    args := #["UserProject.usesAxiom", "--import", "UserProject",
              "--config", "full", "--report", "axioms"]
    expectStdout := #["UserProject.userAxiom"]
    rejectStdout := #["Externs ("] }
]

def main : IO UInt32 := do
  -- Verify user project directory exists
  unless (← System.FilePath.pathExists userProjectDir) do
    IO.eprintln s!"Error: user project not found at {userProjectDir}"
    return 1
  -- Build the user project first
  IO.println s!"Building user project at {userProjectDir}..."
  let buildResult ← IO.Process.output {
    cmd := "lake"
    args := #["build", "UserProject"]
    cwd := some userProjectDir
  }
  unless buildResult.exitCode == 0 do
    IO.eprintln s!"Error: failed to build user project:\n{buildResult.stderr}"
    return 1
  IO.println "User project built. Running CLI tests...\n"
  let mut passed := 0
  let mut failed := 0
  for tc in tests do
    if (← runAudit tc) then
      passed := passed + 1
    else
      failed := failed + 1
  IO.println s!"\nCLI tests: {passed} passed, {failed} failed, {passed + failed} total"
  return if failed == 0 then 0 else 1
