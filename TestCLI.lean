-- Cross-project CLI integration tests for `lake exe audit`.
-- Tests run from test-packages/user-project/, which `require`s lean4-dep-audit,
-- simulating a real user's project. Invokes `lake exe lean4-dep-audit/audit`.
--
-- Run: `lake build audit && lake build test_cli && lake exe test_cli`

import Lean
import Lean4DepAudit

open Lean Lean4DepAudit

-- ============================================================================
-- Test infrastructure
-- ============================================================================

/-- The user project directory where we simulate a real user running the auditor. -/
def userProjectDir : String := "test-packages/user-project"

/-- Run `lake exe lean4-dep-audit/audit <args>` from the user project directory. -/
def execAudit (args : Array String) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := "lake"
    args := #["exe", "lean4-dep-audit/audit"] ++ args
    cwd := some userProjectDir
  }

-- ============================================================================
-- Substring-based tests (for YAML output, error cases, help text)
-- ============================================================================

structure SubstrTest where
  name : String
  args : Array String
  expectExit : UInt32 := 0
  expectStdout : Array String := #[]
  expectStderr : Array String := #[]
  rejectStdout : Array String := #[]

def runSubstrTest (tc : SubstrTest) : IO Bool := do
  let result ← execAudit tc.args
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

-- ============================================================================
-- JSON round-trip tests (deserialize stdout into AuditResultSer)
-- ============================================================================

structure JsonTest where
  name : String
  args : Array String
  /-- Validation function on the deserialized result. Return error message on failure. -/
  validate : AuditResultSer → Except String Unit

def runJsonTest (tc : JsonTest) : IO Bool := do
  let result ← execAudit (tc.args ++ #["--format", "json"])
  if result.exitCode != 0 then
    IO.eprintln s!"FAIL [{tc.name}]: non-zero exit code {result.exitCode}"
    IO.eprintln s!"  stderr: {result.stderr.take 300}"
    return false
  let stdout := result.stdout.trimAscii.toString
  match Json.parse stdout with
  | .error e =>
    IO.eprintln s!"FAIL [{tc.name}]: JSON parse error: {e}"
    IO.eprintln s!"  stdout: {stdout.take 300}"
    return false
  | .ok json =>
    match fromJson? json with
    | .error e =>
      IO.eprintln s!"FAIL [{tc.name}]: FromJson error: {e}"
      IO.eprintln s!"  json: {stdout.take 300}"
      return false
    | .ok (r : AuditResultSer) =>
      match tc.validate r with
      | .ok () =>
        IO.println s!"PASS: {tc.name}"
        return true
      | .error msg =>
        IO.eprintln s!"FAIL [{tc.name}]: {msg}"
        return false

-- ============================================================================
-- Helper predicates for JSON validation
-- ============================================================================

def hasFindings (r : AuditResultSer) (n : Nat) : Except String Unit :=
  if r.findings.size == n then .ok ()
  else .error s!"expected {n} findings, got {r.findings.size}"

def hasFindingNamed (r : AuditResultSer) (name : Name) : Except String Unit :=
  if r.findings.any (·.name == name) then .ok ()
  else .error s!"expected finding named '{name}'"

def noFindingNamed (r : AuditResultSer) (name : Name) : Except String Unit :=
  if r.findings.any (·.name == name) then .error s!"expected no finding named '{name}'"
  else .ok ()

def findingIsExtern (r : AuditResultSer) (name : Name) (sym : String) : Except String Unit :=
  match r.findings.find? (·.name == name) with
  | some fi =>
    if fi.finding == .extern_ sym then .ok ()
    else .error s!"expected '{name}' to be extern \"{sym}\", got {repr fi.finding}"
  | none => .error s!"finding '{name}' not present"

def findingIsAxiom (r : AuditResultSer) (name : Name) : Except String Unit :=
  match r.findings.find? (·.name == name) with
  | some fi =>
    if fi.finding == .axiom_ then .ok ()
    else .error s!"expected '{name}' to be axiom, got {repr fi.finding}"
  | none => .error s!"finding '{name}' not present"

def hasDrill (r : AuditResultSer) (target : Name) : Except String Unit :=
  if r.drill.any (·.target == target) then .ok ()
  else .error s!"expected drill with target '{target}'"

def drillHasChild (r : AuditResultSer) (target child : Name) : Except String Unit :=
  match r.drill.find? (·.target == target) with
  | some dr =>
    if dr.children.any (· == child) then .ok ()
    else .error s!"expected drill to '{target}' to include child '{child}'"
  | none => .error s!"no drill with target '{target}'"

/-- Sequence multiple checks. -/
def checks (cs : List (Except String Unit)) : Except String Unit :=
  cs.foldl (init := .ok ()) fun acc c =>
    match acc with
    | .error e => .error e
    | .ok ()   => c

-- ============================================================================
-- Test definitions
-- ============================================================================

def substrTests : Array SubstrTest := #[
  -- Basic CLI behavior
  { name := "help flag"
    args := #["--help"]
    expectStdout := #["Usage:", "--import", "--config", "--format", "Filter DSL:"] },
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
  { name := "bad format"
    args := #["foo", "--import", "UserProject", "--format", "xml"]
    expectExit := 1
    expectStderr := #["unknown format"] },
  { name := "nonexistent constant"
    args := #["NoSuchConst", "--import", "UserProject"]
    expectStderr := #["not found in environment"]
    expectStdout := #["findings: []"] },

  -- YAML output tests
  { name := "yaml: pure function 0 findings"
    args := #["UserProject.pureFunction", "--import", "UserProject"]
    expectStdout := #["findings: []"] },
  { name := "yaml: standard config finds extern"
    args := #["UserProject.callsExtern", "--import", "UserProject"]
    expectStdout := #["name: UserProject.userExternFn", "user_custom_ffi"] },
  { name := "yaml: standard config finds axiom"
    args := #["UserProject.usesAxiom", "--import", "UserProject"]
    expectStdout := #["name: UserProject.userAxiom", "kind: axiom"] },
  { name := "yaml: drill-down"
    args := #["UserProject.userMain", "--import", "UserProject",
              "--config", "full", "--drill", "UserProject.userExternFn"]
    expectStdout := #["drill:", "target: UserProject.userExternFn",
                       "UserProject.callsExtern"] },
  { name := "yaml: DSL externs only"
    args := #["UserProject.userMain", "--import", "UserProject",
              "--config", "full", "--report", "externs"]
    expectStdout := #["user_custom_ffi"]
    rejectStdout := #["kind: axiom"] },
  { name := "yaml: DSL axioms only"
    args := #["UserProject.usesAxiom", "--import", "UserProject",
              "--config", "full", "--report", "axioms"]
    expectStdout := #["UserProject.userAxiom"]
    rejectStdout := #["kind: extern"] },

  -- Provenance YAML tests
  { name := "yaml: provenance UNRESOLVED for user extern"
    args := #["UserProject.callsExtern", "--import", "UserProject"]
    expectStdout := #["provenance: UNRESOLVED"] },
  { name := "yaml: provenance toolchain-runtime for stdlib extern"
    args := #["String.append", "--import", "Init", "--config", "full"]
    expectStdout := #["provenance: toolchain-runtime"] },
  { name := "yaml: provenance toolchain-header for header-only extern"
    args := #["String.append", "--import", "Init", "--config", "full"]
    expectStdout := #["provenance: toolchain-header"] }
]

def jsonTests : Array JsonTest := #[
  -- Zero findings
  { name := "json: pure function 0 findings"
    args := #["UserProject.pureFunction", "--import", "UserProject"]
    validate := fun r => checks [
      hasFindings r 0,
      if r.audited == #[`UserProject.pureFunction] then .ok ()
      else .error s!"wrong audited: {r.audited.map Name.toString}"
    ] },

  -- Standard config finds extern
  { name := "json: standard config finds extern"
    args := #["UserProject.callsExtern", "--import", "UserProject"]
    validate := fun r => checks [
      hasFindings r 1,
      findingIsExtern r `UserProject.userExternFn "user_custom_ffi"
    ] },

  -- Standard config finds axiom
  { name := "json: standard config finds axiom"
    args := #["UserProject.usesAxiom", "--import", "UserProject"]
    validate := fun r => checks [
      hasFindingNamed r `UserProject.userAxiom,
      findingIsAxiom r `UserProject.userAxiom
    ] },

  -- Full config on IO action
  { name := "json: full config on IO"
    args := #["UserProject.userMain", "--import", "UserProject", "--config", "full"]
    validate := fun r => checks [
      hasFindingNamed r `UserProject.userExternFn,
      findingIsExtern r `UserProject.userExternFn "user_custom_ffi",
      -- Should have more findings from stdlib in full config
      if r.findings.size > 1 then .ok ()
      else .error s!"expected >1 findings in full config, got {r.findings.size}"
    ] },

  -- Drill-down
  { name := "json: drill-down to extern"
    args := #["UserProject.userMain", "--import", "UserProject",
              "--config", "full", "--drill", "UserProject.userExternFn"]
    validate := fun r => checks [
      hasDrill r `UserProject.userExternFn,
      drillHasChild r `UserProject.userExternFn `UserProject.callsExtern
    ] },

  -- Multiple constants
  { name := "json: multi constant"
    args := #["UserProject.callsExtern", "UserProject.usesAxiom",
              "--import", "UserProject", "--config", "full"]
    validate := fun r => checks [
      if r.audited.size == 2 then .ok ()
      else .error s!"expected 2 audited constants, got {r.audited.size}",
      hasFindingNamed r `UserProject.userExternFn,
      hasFindingNamed r `UserProject.userAxiom
    ] },

  -- DSL: externs only (no axioms)
  { name := "json: DSL externs only"
    args := #["UserProject.userMain", "--import", "UserProject",
              "--config", "full", "--report", "externs"]
    validate := fun r => checks [
      hasFindingNamed r `UserProject.userExternFn,
      -- All findings should be externs
      if r.findings.all (fun fi => match fi.finding with | .extern_ _ => true | _ => false)
      then .ok ()
      else .error "expected all findings to be externs"
    ] },

  -- DSL: externs & !stdlib (only user externs)
  { name := "json: DSL externs & !stdlib"
    args := #["UserProject.userMain", "--import", "UserProject",
              "--config", "full", "--report", "externs & !stdlib"]
    validate := fun r => checks [
      hasFindingNamed r `UserProject.userExternFn,
      -- Should not have any stdlib externs
      if r.findings.all (fun fi => fi.name.toString.startsWith "UserProject")
      then .ok ()
      else .error "expected only UserProject findings, got stdlib leakage"
    ] },

  -- DSL: axioms only (no externs)
  { name := "json: DSL axioms only"
    args := #["UserProject.usesAxiom", "--import", "UserProject",
              "--config", "full", "--report", "axioms"]
    validate := fun r => checks [
      findingIsAxiom r `UserProject.userAxiom,
      -- All findings should be axioms
      if r.findings.all (fun fi => fi.finding == .axiom_)
      then .ok ()
      else .error "expected all findings to be axioms"
    ] },

  -- Type info present
  { name := "json: type field populated"
    args := #["UserProject.callsExtern", "--import", "UserProject"]
    validate := fun r =>
      match r.findings.find? (·.name == `UserProject.userExternFn) with
      | some fi =>
        if fi.type != "unknown" && fi.type != "" then .ok ()
        else .error s!"expected non-empty type, got \"{fi.type}\""
      | none => .error "finding not present" },

  -- Round-trip: visited > 0
  { name := "json: visited count"
    args := #["UserProject.callsExtern", "--import", "UserProject"]
    validate := fun r =>
      if r.visited > 0 then .ok ()
      else .error "expected visited > 0" },

  -- Provenance: user extern is unresolved
  { name := "json: provenance unresolved for user extern"
    args := #["UserProject.callsExtern", "--import", "UserProject"]
    validate := fun r =>
      match r.findings.find? (·.name == `UserProject.userExternFn) with
      | some fi =>
        match fi.provenance? with
        | some .unresolved => .ok ()
        | some other => .error s!"expected unresolved provenance, got {repr other}"
        | none => .error "expected provenance to be set, got none"
      | none => .error "finding not present" },

  -- Provenance: stdlib externs have toolchainRuntime or toolchainHeader
  { name := "json: provenance populated for stdlib externs"
    args := #["String.append", "--import", "Init", "--config", "full"]
    validate := fun r =>
      let externFindings := r.findings.filter fun fi =>
        match fi.finding with | .extern_ _ => true | _ => false
      if externFindings.isEmpty then .error "expected some extern findings"
      else
        -- Every extern finding should have provenance set
        let allHaveProv := externFindings.all fun fi => fi.provenance?.isSome
        if !allHaveProv then .error "some extern findings have no provenance"
        else .ok ()
  }
]

-- ============================================================================
-- Main
-- ============================================================================

def main : IO UInt32 := do
  unless (← System.FilePath.pathExists userProjectDir) do
    IO.eprintln s!"Error: user project not found at {userProjectDir}"
    return 1
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
  for tc in substrTests do
    if (← runSubstrTest tc) then passed := passed + 1 else failed := failed + 1
  for tc in jsonTests do
    if (← runJsonTest tc) then passed := passed + 1 else failed := failed + 1
  IO.println s!"\nCLI tests: {passed} passed, {failed} failed, {passed + failed} total"
  return if failed == 0 then 0 else 1
