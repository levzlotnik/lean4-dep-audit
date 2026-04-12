-- CLI module: filter DSL parser + argument handling + formatted output.
import Lean
import MyLeanTermAuditor.Types
import MyLeanTermAuditor.Filter
import MyLeanTermAuditor.Traverse
import MyLeanTermAuditor.Monad
import MyLeanTermAuditor.ExternSourceProvenance
import MyLeanTermAuditor.ExternCAudit

open Lean
open MyLeanTermAuditor

namespace MyLeanTermAuditor.CLI

-- ============================================================================
-- Filter DSL: Tokenizer
-- ============================================================================

inductive Token where
  | ident  (s : String)
  | lparen
  | rparen
  | and_
  | or_
  | not_
  | eof
  deriving Repr, BEq

private partial def scanIdent (chars : Array Char) (i : Nat) : Nat :=
  if i >= chars.size then i
  else
    let c := chars[i]!
    if c.isAlpha || c.isDigit || c == '_' then scanIdent chars (i + 1)
    else i

partial def tokenize (input : String) : Except String (Array Token) :=
  let chars := input.toList.toArray
  go chars 0 #[]
where
  go (chars : Array Char) (i : Nat) (tokens : Array Token) : Except String (Array Token) :=
    if i >= chars.size then
      return tokens.push .eof
    else
      let c := chars[i]!
      if c == ' ' || c == '\t' then go chars (i + 1) tokens
      else if c == '(' then go chars (i + 1) (tokens.push .lparen)
      else if c == ')' then go chars (i + 1) (tokens.push .rparen)
      else if c == '&' then go chars (i + 1) (tokens.push .and_)
      else if c == '|' then go chars (i + 1) (tokens.push .or_)
      else if c == '!' then go chars (i + 1) (tokens.push .not_)
      else if c.isAlpha || c == '_' then
        let j := scanIdent chars i
        let word := String.ofList ((chars.toList.drop i).take (j - i))
        go chars j (tokens.push (.ident word))
      else
        .error s!"unexpected character '{c}' in filter expression"

-- ============================================================================
-- Filter DSL: Parser infrastructure
-- ============================================================================

structure ParseState where
  tokens : Array Token
  pos    : Nat := 0

def ParseState.peek (s : ParseState) : Token :=
  s.tokens.getD s.pos .eof

def ParseState.advance (s : ParseState) : ParseState :=
  { s with pos := s.pos + 1 }

def ParseState.expect (s : ParseState) (t : Token) : Except String ParseState :=
  if s.peek == t then .ok s.advance
  else .error s!"expected {repr t}, got {repr s.peek}"

def resolveReportAtom (name : String) : Except String (ConstContext → Bool) :=
  match name with
  | "axioms"        => .ok Filter.axiomsOnly
  | "opaques"       => .ok Filter.opaquesOnly
  | "partials"      => .ok Filter.partialsOnly
  | "externs"       => .ok Filter.externsOnly
  | "initialize"    => .ok Filter.initializeOnly
  | "runtime"       => .ok Filter.runtimeOnly
  | "kernel"        => .ok Filter.kernelOnly
  | "stdlib"        => .ok Filter.isStandardLibrary
  | "hasFinding"    => .ok Filter.hasAnyFinding
  | "nonStdAxioms"  => .ok Filter.nonStandardAxiomsOnly
  | "nonStdExterns" => .ok Filter.nonStandardExternsOnly
  | "nonStdOpaques" => .ok Filter.nonStandardOpaquesOnly
  | other           => .error s!"unknown report atom '{other}'"

def resolveDescendAtom (name : String) : Except String (DescendContext → Bool) :=
  match name with
  | "skipProofs" => .ok Descend.skipProofTerms
  | "skipTypes"  => .ok Descend.skipTypes
  | "all"        => .ok Descend.all
  | other        => .error s!"unknown descend atom '{other}'"

-- ============================================================================
-- ConstContext filter parser (mutual recursion)
-- ============================================================================

mutual
  partial def parseReportExpr (s : ParseState) :
      Except String (ParseState × (ConstContext → Bool)) := do
    let (s, f) ← parseReportTerm s
    parseReportExprTail s f

  partial def parseReportExprTail (s : ParseState) (f : ConstContext → Bool) :
      Except String (ParseState × (ConstContext → Bool)) :=
    if s.peek == .and_ then do
      let (s, g) ← parseReportTerm s.advance
      parseReportExprTail s (Filter.and f g)
    else if s.peek == .or_ then do
      let (s, g) ← parseReportTerm s.advance
      parseReportExprTail s (Filter.or f g)
    else
      .ok (s, f)

  partial def parseReportTerm (s : ParseState) :
      Except String (ParseState × (ConstContext → Bool)) :=
    if s.peek == .not_ then do
      let (s, f) ← parseReportTerm s.advance
      .ok (s, Filter.not f)
    else
      parseReportAtomP s

  partial def parseReportAtomP (s : ParseState) :
      Except String (ParseState × (ConstContext → Bool)) :=
    match s.peek with
    | .ident name => do
      let f ← resolveReportAtom name
      .ok (s.advance, f)
    | .lparen => do
      let (s, f) ← parseReportExpr s.advance
      let s ← s.expect .rparen
      .ok (s, f)
    | tok => .error s!"expected identifier or '(', got {repr tok}"
end

def parseReportFilter (input : String) : Except String (ConstContext → Bool) := do
  let tokens ← tokenize input
  let (s, f) ← parseReportExpr { tokens }
  if s.peek != .eof then
    .error s!"unexpected token after expression: {repr s.peek}"
  else
    .ok f

-- ============================================================================
-- DescendContext filter parser
-- ============================================================================

mutual
  partial def parseDescendExpr (s : ParseState) :
      Except String (ParseState × (DescendContext → Bool)) := do
    let (s, f) ← parseDescendTerm s
    parseDescendExprTail s f

  partial def parseDescendExprTail (s : ParseState) (f : DescendContext → Bool) :
      Except String (ParseState × (DescendContext → Bool)) :=
    if s.peek == .and_ then do
      let (s, g) ← parseDescendTerm s.advance
      parseDescendExprTail s (Descend.and f g)
    else if s.peek == .or_ then do
      let (s, g) ← parseDescendTerm s.advance
      parseDescendExprTail s (Descend.or f g)
    else
      .ok (s, f)

  partial def parseDescendTerm (s : ParseState) :
      Except String (ParseState × (DescendContext → Bool)) :=
    if s.peek == .not_ then do
      let (s, f) ← parseDescendTerm s.advance
      .ok (s, fun ctx => !f ctx)
    else
      parseDescendAtomP s

  partial def parseDescendAtomP (s : ParseState) :
      Except String (ParseState × (DescendContext → Bool)) :=
    match s.peek with
    | .ident name => do
      let f ← resolveDescendAtom name
      .ok (s.advance, f)
    | .lparen => do
      let (s, f) ← parseDescendExpr s.advance
      let s ← s.expect .rparen
      .ok (s, f)
    | tok => .error s!"expected identifier or '(', got {repr tok}"
end

def parseDescendFilter (input : String) : Except String (DescendContext → Bool) := do
  let tokens ← tokenize input
  let (s, f) ← parseDescendExpr { tokens }
  if s.peek != .eof then
    .error s!"unexpected token after expression: {repr s.peek}"
  else
    .ok f

-- ============================================================================
-- Named config presets
-- ============================================================================

def resolveConfigPreset (name : String) : Except String AuditConfig :=
  match name with
  | "standard"       => .ok AuditConfig.standard
  | "full"           => .ok AuditConfig.default
  | "runtimeOnly"    => .ok AuditConfig.runtimeOnly
  | "runtimeExterns" => .ok AuditConfig.runtimeExterns
  | "axiomsOnly"     => .ok AuditConfig.axiomsOnly
  | other            => .error s!"unknown config preset '{other}'"

-- ============================================================================
-- CLI Argument Parsing
-- ============================================================================

structure CLIArgs where
  names       : Array String := #[]
  imports     : Array String := #[]
  config      : Option String := none
  reportExpr  : Option String := none
  recurseExpr : Option String := none
  descendExpr : Option String := none
  drill       : Array String := #[]
  format      : Option String := none
  help        : Bool := false
  deriving Repr

partial def parseArgs (args : List String) : Except String CLIArgs :=
  go args {}
where
  go : List String → CLIArgs → Except String CLIArgs
    | [], result => .ok result
    | ("--help" :: rest), result => go rest { result with help := true }
    | ("-h" :: rest), result => go rest { result with help := true }
    | ("--import" :: val :: rest), result =>
        go rest { result with imports := result.imports.push val }
    | ("--import" :: []), _ => .error "--import requires a value"
    | ("--config" :: val :: rest), result =>
        go rest { result with config := some val }
    | ("--config" :: []), _ => .error "--config requires a value"
    | ("--report" :: val :: rest), result =>
        go rest { result with reportExpr := some val }
    | ("--report" :: []), _ => .error "--report requires a value"
    | ("--recurse" :: val :: rest), result =>
        go rest { result with recurseExpr := some val }
    | ("--recurse" :: []), _ => .error "--recurse requires a value"
    | ("--descend" :: val :: rest), result =>
        go rest { result with descendExpr := some val }
    | ("--descend" :: []), _ => .error "--descend requires a value"
    | ("--drill" :: val :: rest), result =>
        go rest { result with drill := result.drill.push val }
    | ("--drill" :: []), _ => .error "--drill requires a value"
    | ("--format" :: val :: rest), result =>
        go rest { result with format := some val }
    | ("--format" :: []), _ => .error "--format requires a value"
    | (arg :: rest), result =>
        if arg.startsWith "--" then .error s!"unknown option '{arg}'"
        else go rest { result with names := result.names.push arg }

def buildConfig (args : CLIArgs) : Except String AuditConfig := do
  let base ← match args.config with
    | some preset => resolveConfigPreset preset
    | none        => .ok AuditConfig.standard
  let report ← match args.reportExpr with
    | some expr => parseReportFilter expr
    | none      => .ok base.shouldReport
  let recurse ← match args.recurseExpr with
    | some expr => parseReportFilter expr
    | none      => .ok base.shouldRecurse
  let descend ← match args.descendExpr with
    | some expr => parseDescendFilter expr
    | none      => .ok base.shouldDescend
  let drillNames := args.drill.toList.map String.toName
  return {
    shouldReport  := report
    shouldRecurse := recurse
    shouldDescend := descend
    drill         := drillNames
  }

-- ============================================================================
-- Output format enum
-- ============================================================================

inductive OutputFormat where
  | yaml
  | json
  deriving BEq

def resolveFormat (s : String) : Except String OutputFormat :=
  match s with
  | "yaml" => .ok .yaml
  | "json" => .ok .json
  | other  => .error s!"unknown format '{other}' (expected: yaml, json)"

-- ============================================================================
-- Shared helpers
-- ============================================================================

private def findingKind (fi : FindingInfo) : String :=
  match fi.finding with
  | .axiom_      => "axiom"
  | .opaque_ k   => s!"opaque ({k})"
  | .extern_ sym => s!"extern \"{sym}\""

private def findingReachability (fi : FindingInfo) : String :=
  match fi.reachableAtRuntime, fi.reachableInProof with
  | true, true  => "runtime, kernel"
  | true, false => "runtime"
  | false, true => "kernel"
  | false, false => ""

-- ============================================================================
-- YAML-like formatter (default)
-- ============================================================================

private def yamlFinding (fi : FindingInfo) : String :=
  let typeStr := if fi.typeStr.isEmpty then "unknown" else fi.typeStr
  let cLine := match fi.typeCheck with
    | .compatible l | .mismatch _ l => if l > 0 then some l else none
    | _ => none
  let provStr := match fi.provenance? with
    | some (.tracedToSource c _o _a) =>
      let loc := match cLine with | some l => s!"{c}:{l}" | none => c
      s!"\n    provenance: traced \"{loc}\""
    | some (.toolchainRuntime l) => s!"\n    provenance: toolchain-runtime \"{l}\""
    | some .toolchainHeader =>
      let loc := match cLine with | some l => s!"lean.h:{l}" | none => "lean.h"
      s!"\n    provenance: toolchain-header ({loc})"
    | some (.binaryOnly l) => s!"\n    provenance: BINARY-ONLY \"{l}\""
    | some .unresolved => s!"\n    provenance: UNRESOLVED"
    | none => ""
  let typeCheckStr := match fi.typeCheck with
    | .compatible _ => s!"\n    type-check: compatible"
    | .mismatch d _ => s!"\n    type-check: MISMATCH {d}"
    | .unparseable r => s!"\n    type-check: UNPARSEABLE ({r})"
    | .notChecked => ""
  s!"  - name: {fi.name}\n" ++
  s!"    kind: {findingKind fi}\n" ++
  s!"    type: \"{typeStr}\"\n" ++
  s!"    reachability: {findingReachability fi}\n" ++
  s!"    location: \"{fi.location}\"\n" ++
  s!"    encounters: {fi.numEncounters}" ++
  provStr ++
  typeCheckStr

private def yamlDrill (dr : DrillResult) : String :=
  if dr.children.isEmpty then
    s!"  - from: {dr.from_}\n" ++
    s!"    target: {dr.target}\n" ++
    s!"    children: []"
  else
    let childLines := dr.children.map fun c => s!"      - {c}"
    s!"  - from: {dr.from_}\n" ++
    s!"    target: {dr.target}\n" ++
    s!"    children:\n" ++
    "\n".intercalate childLines

def formatYaml (result : AuditResult) (names : Array Name)
    (drills : Array DrillResult := #[]) : String :=
  let nameLines := names.toList.map fun n => s!"  - {n}"
  let out := s!"audited:\n" ++
    "\n".intercalate nameLines ++ "\n" ++
    s!"visited: {result.numVisited}\n"
  let all := result.findingsArray
  let out := if all.isEmpty then
    out ++ "findings: []"
  else
    let findingLines := all.toList.map yamlFinding
    out ++ s!"findings:\n" ++ "\n".intercalate findingLines
  let out := if drills.isEmpty then out
  else
    let drillLines := drills.toList.map yamlDrill
    out ++ s!"\ndrill:\n" ++ "\n".intercalate drillLines
  out

-- ============================================================================
-- JSON formatter (compressed, via ToJson instances)
-- ============================================================================

def formatJson (result : AuditResult) (names : Array Name)
    (drills : Array DrillResult := #[]) : String :=
  (toJson (result.serialize names drills)).compress

-- ============================================================================
-- Help text
-- ============================================================================

def helpText : String := String.intercalate "\n" [
  "Usage: lake exe audit <constant> [<constant>...] --import <module> [options]",
  "",
  "Arguments:",
  "  <constant>               Fully qualified constant name(s) to audit",
  "",
  "Required:",
  "  --import <module>        Module(s) to import (repeat for multiple)",
  "",
  "Options:",
  "  --config <preset>        standard, full, runtimeOnly, runtimeExterns, axiomsOnly",
  "  --report <expr>          Filter DSL expression for reporting (overrides config)",
  "  --recurse <expr>         Filter DSL expression for recursion (overrides config)",
  "  --descend <expr>         Filter DSL expression for descent (overrides config)",
  "  --drill <name>           Drill-down target (repeat for multiple)",
  "  --format <fmt>           Output format: yaml (default), json",
  "  --help                   Show this help",
  "",
  "Filter DSL:",
  "  Report atoms:  axioms opaques partials externs initialize runtime kernel",
  "                 stdlib hasFinding nonStdAxioms nonStdExterns nonStdOpaques",
  "  Descend atoms: skipProofs skipTypes all",
  "  Operators:     & (and)  | (or)  ! (not)  () (grouping)",
  "",
  "Examples:",
  "  lake exe audit myMain --import MyModule",
  "  lake exe audit myMain --import MyModule --config standard --format json",
  "  lake exe audit myMain --import MyModule --report 'externs & runtime' --descend skipProofs",
  "  lake exe audit myMain --import MyModule --drill propext --drill Quot.sound"]

-- ============================================================================
-- Main entry point
-- ============================================================================

def run (args : List String) : IO UInt32 := do
  let cliArgs ← match parseArgs args with
    | .ok a    => pure a
    | .error e =>
      IO.eprintln s!"Error: {e}"
      return (1 : UInt32)
  if cliArgs.help then
    IO.println helpText
    return 0
  if cliArgs.names.isEmpty then
    IO.eprintln "Error: no constants specified. Use --help for usage."
    return (1 : UInt32)
  if cliArgs.imports.isEmpty then
    IO.eprintln "Error: no imports specified. Use --import <module>."
    return (1 : UInt32)
  let config ← match buildConfig cliArgs with
    | .ok c    => pure c
    | .error e =>
      IO.eprintln s!"Error: {e}"
      return (1 : UInt32)
  let fmt ← match cliArgs.format with
    | some f => match resolveFormat f with
      | .ok f    => pure f
      | .error e =>
        IO.eprintln s!"Error: {e}"
        return (1 : UInt32)
    | none => pure OutputFormat.yaml
  -- Initialize Lean environment
  let imports := cliArgs.imports.map fun m =>
    { module := String.toName m : Import }
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← try
    importModules imports.toList.toArray {} (trustLevel := 0)
  catch e =>
    IO.eprintln s!"Error importing modules: {e}"
    return (1 : UInt32)
  -- Run audit (pure first pass)
  let names := cliArgs.names.map String.toName
  let mut result : AuditResult := {}
  for name in names do
    match env.find? name with
    | some _ => result := auditConst env config name result
    | none   =>
      IO.eprintln s!"Warning: constant '{name}' not found in environment, skipping."
  -- Resolve source locations via MetaM
  let resolved ← do
    let coreCtx : Core.Context := {
      fileName := "<cli>"
      fileMap := .ofString ""
    }
    let coreState : Core.State := { env }
    let act : EIO Exception _ := (resolveLocations result).run.run coreCtx coreState
    let eiResult ← act.toIO'
    match eiResult with
    | .ok ((r, _), _) => pure r
    | .error _         => pure result
  -- Resolve extern symbol provenance
  let resolved ← resolveProvenance resolved (← Lean.searchPathRef.get)
  -- Audit C type compatibility
  let sysroot ← try Lean.findSysroot catch _ => pure (System.FilePath.mk "")
  let resolved ← resolveTypeAudit resolved env sysroot
  -- Collect drill-down results
  let mut drills : Array DrillResult := #[]
  for target in config.drill do
    for name in names do
      drills := drills.push (drillDown env name target resolved)
  -- Print output
  match fmt with
  | .yaml => IO.println (formatYaml resolved names drills)
  | .json => IO.println (formatJson resolved names drills)
  return 0

end MyLeanTermAuditor.CLI
