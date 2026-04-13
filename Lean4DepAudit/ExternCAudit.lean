/-
  ExternCAudit: C function signature parser and Lean-to-C type compatibility checker.

  When an `@[extern]` symbol has been traced to a `.c` source file (by ExternSourceProvenance),
  this module:
  1. Finds the function definition in the C source
  2. Parses its C return type and parameter types
  3. Maps the Lean declared type to expected C types via the Lean FFI ABI
  4. Compares — mismatch = critical audit finding

  If the parser can't handle a signature, it reports `unparseable` rather than
  guessing — the user can then inspect the C source manually.
-/
import Lean
import Lean4DepAudit.Types

open Lean Meta System

namespace Lean4DepAudit

-- ============================================================================
-- Part 1: C Type representation
-- ============================================================================

/-- A C type as it appears in a function signature. -/
inductive CType where
  | uint8   -- uint8_t
  | uint16  -- uint16_t
  | uint32  -- uint32_t
  | uint64  -- uint64_t
  | sizeT   -- size_t
  | double  -- double
  | leanObj -- lean_object*, lean_obj_arg, lean_obj_res, b_lean_obj_arg, b_lean_obj_res
  | void    -- void (only as return type)
  | unknown (raw : String) -- couldn't classify
  deriving Repr, BEq, Inhabited

instance : ToString CType where
  toString
    | .uint8        => "uint8_t"
    | .uint16       => "uint16_t"
    | .uint32       => "uint32_t"
    | .uint64       => "uint64_t"
    | .sizeT        => "size_t"
    | .double       => "double"
    | .leanObj      => "lean_object*"
    | .void         => "void"
    | .unknown raw  => s!"unknown({raw})"

-- ============================================================================
-- Part 2: C type classifier
-- ============================================================================

/-- Classify a C type token string into a CType. -/
def classifyCType (s : String) : CType :=
  match s with
  | "uint8_t"        => .uint8
  | "uint16_t"       => .uint16
  | "uint32_t"       => .uint32
  | "uint64_t"       => .uint64
  | "size_t"         => .sizeT
  | "double"         => .double
  | "lean_object*"   => .leanObj
  | "lean_obj_arg"   => .leanObj
  | "lean_obj_res"   => .leanObj
  | "b_lean_obj_arg" => .leanObj
  | "b_lean_obj_res" => .leanObj
  | "void"           => .void
  | other            => .unknown other

-- ============================================================================
-- Part 3: C function signature parser
-- ============================================================================

/-- A parsed C function signature. -/
structure CFuncSig where
  returnType : CType
  name : String
  params : Array CType
  /-- 1-indexed line number in the source file where this function was found. -/
  line : Nat := 0
  deriving Repr, BEq, Inhabited

instance : ToString CFuncSig where
  toString sig :=
    let paramStr := ", ".intercalate (sig.params.toList.map toString)
    s!"{sig.returnType} {sig.name}({paramStr})"

/-- Result of trying to find and parse a C function in a source file. -/
inductive CParseResult where
  | found (sig : CFuncSig)
  | notFound          -- symbol name not found in file at all
  | unparseable (line : String) -- found the symbol but couldn't parse the signature cleanly
  deriving Repr



/-- Prefixes to strip from C function declarations. -/
private def stripPrefixes : List String :=
  ["LEAN_EXPORT", "LEAN_ALWAYS_INLINE", "static", "inline"]

/-- Strip known prefixes (LEAN_EXPORT, static, inline, LEAN_ALWAYS_INLINE) from tokens. -/
private def stripKnownPrefixes (tokens : List String) : List String :=
  tokens.filter fun t => !stripPrefixes.contains t

/-- Normalize pointer types: merge `type` followed by `*` into `type*`,
    and handle `type*` as-is. Also handle `type` `*name` patterns. -/
private partial def normalizePointerTokens (tokens : List String) : List String :=
  go tokens []
where
  go : List String → List String → List String
    | [], acc => acc.reverse
    | [t], acc => (t :: acc).reverse
    | t :: next :: rest, acc =>
      if next == "*" then
        -- `type *` → `type*`
        go rest ((t ++ "*") :: acc)
      else if next.startsWith "*" then
        -- `type *name` → merge type with *, leave name
        go ((next.drop 1).toString :: rest) ((t ++ "*") :: acc)
      else
        go (next :: rest) (t :: acc)

/-- Split a string by whitespace into non-empty tokens. -/
private def splitWhitespace (s : String) : List String :=
  let parts := s.splitOn " "
  let parts := parts.foldl (fun acc p => acc ++ p.splitOn "\t") []
  parts.filter (· != "")

/-- Parse a single C parameter string like "uint32_t a" or "lean_obj_arg unit".
    Returns the type (strips the parameter name = last token). -/
private def parseParamType (param : String) : CType :=
  let tokens := splitWhitespace param.trimAscii.toString
  -- Normalize pointer patterns
  let tokens := normalizePointerTokens tokens
  match tokens with
  | [] => .unknown ""
  | ["void"] => .void
  | [single] =>
    -- Could be a typedef like "lean_obj_arg" used without a param name
    -- (shouldn't happen in well-formed C, but handle gracefully)
    classifyCType single
  | _ =>
    -- Last token is param name, everything before is the type
    -- For simple types: "uint32_t a" → type = "uint32_t"
    -- For pointer types (after normalization): "lean_object* a" → type = "lean_object*"
    let typeTokens := tokens.dropLast
    let typeStr := " ".intercalate typeTokens
    -- Special case: if the merged type is like "lean_object*", classify directly
    classifyCType typeStr

/-- Find the index of the first occurrence of a character in a list. -/
private def findCharIdx (chars : List Char) (c : Char) : Option Nat :=
  go chars 0
where
  go : List Char → Nat → Option Nat
    | [], _ => none
    | x :: rest, i => if x == c then some i else go rest (i + 1)

/-- Try to extract the text between the first '(' and the matching ')'. -/
private def extractParenContent (s : String) : Option String :=
  let chars := s.toList
  match findCharIdx chars '(' with
  | none => none
  | some openIdx =>
    let afterOpen := chars.drop (openIdx + 1)
    match findCharIdx afterOpen ')' with
    | none => none
    | some closeIdx =>
      some (String.ofList (afterOpen.take closeIdx))

/-- Extract the part before '(' — this contains [prefixes] returnType funcName. -/
private def extractBeforeParen (s : String) : String :=
  let chars := s.toList
  match findCharIdx chars '(' with
  | none => s
  | some openIdx => String.ofList (chars.take openIdx)

/-- Try to parse a C function signature from a (possibly multi-line joined) string.
    Expects: [prefixes] <rettype> <funcname>(<params>) [{ ... ]
    Returns none if we can't parse it cleanly. -/
private def tryParseSig (joined : String) (symbol : String) : Option CFuncSig := do
  -- Get parameter content between parens
  let paramContent ← extractParenContent joined
  -- Get the part before parens
  let beforeParen := extractBeforeParen joined
  -- Tokenize and strip prefixes
  let tokens := splitWhitespace beforeParen
  let tokens := stripKnownPrefixes tokens
  -- Normalize pointer types in the prefix part
  let tokens := normalizePointerTokens tokens
  -- We need at least: returnType funcName
  if tokens.length < 2 then none
  else
    -- Last token before '(' should be the function name
    let funcName := tokens.getLast!
    if funcName != symbol then none
    else
      -- Everything before the function name is the return type
      let retTokens := tokens.dropLast
      let retStr := " ".intercalate retTokens
      let retType := classifyCType retStr
      -- Parse parameters
      let params := if paramContent.trimAscii.toString == "void" ||
                       paramContent.trimAscii.toString == "" then
        #[]
      else
        let paramStrs := paramContent.splitOn ","
        paramStrs.toArray.map parseParamType
      some { returnType := retType, name := symbol, params := params }

/-- Find and parse the C function signature for `symbol` in the given source file.
    Looks for lines matching: [LEAN_EXPORT] [LEAN_ALWAYS_INLINE] <rettype> <symbol>(<params>) { -/
def parseCFuncSig (sourceFile : FilePath) (symbol : String) : IO CParseResult := do
  let contents ← try
    IO.FS.readFile sourceFile
  catch _ =>
    return .notFound
  let lines := contents.splitOn "\n"
  let linesArr := lines.toArray
  -- Search for lines containing the symbol followed by '('
  let searchPattern := symbol ++ "("
  let mut foundLine : Option Nat := none
  for i in [:linesArr.size] do
    if linesArr[i]!.hasSubstr searchPattern then
      foundLine := some i
      break
  match foundLine with
  | none => return .notFound
  | some idx =>
    let lineNum := idx + 1  -- 1-indexed
    -- Try the matching line by itself first (most common case)
    match tryParseSig linesArr[idx]! symbol with
    | some sig => return .found { sig with line := lineNum }
    | none =>
      -- Try previous line + matching line (return type on separate line)
      if idx > 0 then
        let twoLines := linesArr[idx - 1]! ++ " " ++ linesArr[idx]!
        match tryParseSig twoLines symbol with
        | some sig => return .found { sig with line := lineNum }
        | none => pure ()
      -- Try a small window (up to 2 lines before and after)
      let startIdx := if idx >= 2 then idx - 2 else 0
      let endIdx := min (idx + 3) linesArr.size
      let window := (linesArr.toList.drop startIdx).take (endIdx - startIdx)
      let joined := " ".intercalate window
      match tryParseSig joined symbol with
      | some sig => return .found { sig with line := lineNum }
      | none => return .unparseable linesArr[idx]!

-- ============================================================================
-- Part 4: Lean type → expected C types
-- ============================================================================

/-- Check if an Expr is a const with the given name. -/
private def isConstNamed (e : Expr) (name : Name) : Bool :=
  match e with
  | .const n _ => n == name
  | _ => false

/-- Map a single Lean type Expr to the expected C type for FFI.
    Handles scalar types, Bool/Decidable (uint8_t), and boxed types (lean_object*). -/
def leanTypeToCType (e : Expr) : CType :=
  match e with
  | .const n _ =>
    if n == ``UInt8  then .uint8
    else if n == ``Bool   then .uint8
    else if n == ``UInt16 then .uint16
    else if n == ``UInt32 then .uint32
    else if n == ``Char   then .uint32
    else if n == ``UInt64 then .uint64
    else if n == ``USize  then .sizeT
    else if n == ``Float  then .double
    else .leanObj  -- Nat, String, any other named type
  -- Decidable _ is compiled as uint8_t by the Lean compiler
  | .app (.const n _) _ =>
    if n == ``Decidable then .uint8
    else .leanObj
  | _ => .leanObj  -- type variables, applications, anything complex = boxed

/-- Check if an Expr represents an IO/BaseIO/EIO type application.
    Returns the inner result type if so. -/
private def getIOInnerType? (e : Expr) : Option Expr :=
  match e with
  | .app (.const n _) inner =>
    if n == ``IO || n == ``BaseIO then some inner
    else none
  | .app (.app (.const n _) _errType) inner =>
    if n == ``EIO then some inner
    else none
  | _ => none

/-- Map a Lean Expr type to expected C return type and parameter types.
    Walks the forall/arrow chain. Returns (params, returnType).
    Skips implicit, strict-implicit, and instance-implicit binders.
    Uses `Meta.isProp` to detect Prop-valued parameters (erased in the FFI ABI). -/
def leanTypeToExpectedCSig (e : Expr) : MetaM (Array CType × CType) :=
  go e #[]
where
  go (e : Expr) (params : Array CType) : MetaM (Array CType × CType) := do
    match e with
    | .forallE _name domain body binderInfo =>
      -- Skip implicit/typeclass parameters — they don't generate C params
      if binderInfo != .default then
        go body params
      -- Skip Prop-valued parameters — erased at the C level
      else if ← Meta.isProp domain then
        go body params
      else
        let paramType := leanTypeToCType domain
        go body (params.push paramType)
    | other =>
      -- This is the return type. Check for IO.
      match getIOInnerType? other with
      | some _innerType =>
        -- IO α: add an extra lean_obj_arg param (world token).
        -- IO always returns lean_obj_res (the world token is wrapped in the result).
        let params := params.push .leanObj
        return (params, .leanObj)
      | none =>
        return (params, leanTypeToCType other)

-- ============================================================================
-- Part 5: Comparator
-- ============================================================================

/-- Result of comparing a parsed C signature against the expected Lean FFI signature. -/
inductive TypeAuditResult where
  | compatible (line : Nat)                  -- all types match; line number in C source
  | mismatch (expected : CFuncSig) (actual : CFuncSig) (details : String) (line : Nat)
  | cSourceNotParseable (reason : String)    -- couldn't parse C source
  | cSourceNotFound                          -- symbol not in C file
  deriving Repr

/-- Check if two CTypes are compatible under FFI rules.
    Scalar types must match exactly; any leanObj matches any leanObj. -/
private def ctypeCompatible (expected actual : CType) : Bool :=
  match expected, actual with
  | .uint8, .uint8   => true
  | .uint16, .uint16 => true
  | .uint32, .uint32 => true
  | .uint64, .uint64 => true
  | .sizeT, .sizeT   => true
  | .double, .double  => true
  | .leanObj, .leanObj => true
  | .void, .void       => true
  | _, _               => false

/-- Compare a parsed C function signature against what Lean expects. -/
def auditExternType (leanType : Expr) (cSig : CFuncSig) : MetaM TypeAuditResult := do
  let (expectedParams, expectedRet) ← leanTypeToExpectedCSig leanType
  let expectedSig : CFuncSig := {
    returnType := expectedRet
    name := cSig.name
    params := expectedParams
  }
  -- Check return type
  if !ctypeCompatible expectedRet cSig.returnType then
    return TypeAuditResult.mismatch expectedSig cSig
      s!"return type: expected {expectedRet}, got {cSig.returnType}" cSig.line
  -- Check parameter count
  else if expectedParams.size != cSig.params.size then
    return TypeAuditResult.mismatch expectedSig cSig
      s!"parameter count: expected {expectedParams.size}, got {cSig.params.size}" cSig.line
  else
    -- Check each parameter
    let mismatchIdx := Id.run do
      for i in [:expectedParams.size] do
        if !ctypeCompatible expectedParams[i]! cSig.params[i]! then
          return some i
      return none
    match mismatchIdx with
    | some i =>
      return TypeAuditResult.mismatch expectedSig cSig
        s!"param {i}: expected {expectedParams[i]!}, got {cSig.params[i]!}" cSig.line
    | none => return TypeAuditResult.compatible cSig.line

-- ============================================================================
-- Part 6: Top-level audit functions
-- ============================================================================

/-- Convert a TypeAuditResult to a CTypeCheckResult for storage in FindingInfo. -/
private def typeAuditToCheck : TypeAuditResult → CTypeCheckResult
  | .compatible line => .compatible (line := line)
  | .mismatch expected actual details line =>
    .mismatch (details := details) (expected := toString expected)
      (actual := toString actual) (line := line)
  | .cSourceNotParseable reason => .unparseable reason
  | .cSourceNotFound => .notChecked

/-- Audit a single extern finding's C type compatibility.
    Reads the C source file, parses the function, compares against Lean type.
    Needs MetaM for `isProp` checks during type mapping. -/
def auditExternCType (fi : FindingInfo) (sysroot : FilePath) : MetaM TypeAuditResult := do
  let symbol := match fi.finding with
    | .extern_ sym => sym
    | _ => ""
  if symbol.isEmpty then return .cSourceNotFound
  let sourceFile := match fi.provenance? with
    | some (.tracedToSource cFile _ _) => FilePath.mk cFile
    | some .toolchainHeader => sysroot / "include" / "lean" / "lean.h"
    | _ => FilePath.mk ""
  if sourceFile.toString.isEmpty then return .cSourceNotFound
  let parseResult ← parseCFuncSig sourceFile symbol
  match parseResult with
  | .found cSig => auditExternType fi.type cSig
  | .notFound => return .cSourceNotFound
  | .unparseable line => return .cSourceNotParseable s!"line: {line}"

/-- Run C type audit on all extern findings that have traced provenance.
    Sets up a MetaM context internally (needs `isProp` for Prop-erasure detection).
    Returns updated AuditResult with typeCheck field populated. -/
def resolveTypeAudit (result : AuditResult) (env : Environment) (sysroot : FilePath)
    : IO AuditResult := do
  let coreCtx : Core.Context := { fileName := "<type-audit>", fileMap := .ofString "" }
  let coreState : Core.State := { env }
  let act : MetaM AuditResult := do
    let mut findings := result.findings
    let findingsArr := result.findingsArray
    for fi in findingsArr do
      match fi.finding with
      | .extern_ _ =>
        let typeResult ← try
          auditExternCType fi sysroot
        catch _ =>
          pure TypeAuditResult.cSourceNotFound
        let check := typeAuditToCheck typeResult
        let updatedFi := { fi with typeCheck := check }
        findings := findings.insert fi.name updatedFi
      | _ => pure ()
    return { result with findings }
  let eiResult ← (act.run.run coreCtx coreState : EIO Exception _).toIO'
  match eiResult with
  | .ok ((r, _), _) => return r
  | .error _ => return result

end Lean4DepAudit
