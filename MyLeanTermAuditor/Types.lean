import Lean

open Lean

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

namespace MyLeanTermAuditor

/-- Sub-classification of opaque constants.
    Lean 4 uses `opaque` in the Environment for several distinct purposes. -/
inductive OpaqueKind where
  /-- `partial def` — has a Lean body, but the kernel can't unfold it (no termination proof). -/
  | partial_
  /-- `initialize` / `builtin_initialize` — value computed at module init time. -/
  | initialize_
  /-- `opaque` with a default body — typically a `NonemptyType` implementation
      or `implemented_by` target. The kernel sees only `@default T inst`. -/
  | implementedBy_
  /-- Catch-all for opaques we haven't classified yet. If you hit this, report it. -/
  | other
  deriving Repr, BEq, Inhabited, ToJson, FromJson

instance : ToString OpaqueKind where
  toString
    | .partial_       => "partial"
    | .initialize_    => "initialize"
    | .implementedBy_ => "implemented_by"
    | .other          => "other"

/-- Classification of a constant that we consider "interesting" for audit purposes. -/
inductive Finding where
  | axiom_    : Finding
  | opaque_   (kind : OpaqueKind) : Finding
  | extern_   (sym : String) : Finding
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- A single step in the expression traversal path, recording how we descended
    from the root expression to a finding. -/
inductive ExprStep where
  | appFn                       -- entered the function of an application
  | appArg                      -- entered the argument of an application
  | lamType                     -- entered the binder type of a lambda
  | lamBody                     -- entered the body of a lambda
  | forallType                  -- entered the binder type of a forall
  | forallBody                  -- entered the body of a forall
  | letType                     -- entered the binder type of a let
  | letVal                      -- entered the value of a let
  | letBody                     -- entered the body of a let
  | mdata                       -- descended through metadata
  | proj                        -- descended through a projection
  | constDef  (name : Name)     -- entered the value (definition) of a looked-up constant
  | constType (name : Name)     -- entered the type of a looked-up constant
  deriving Repr, BEq, Inhabited

/-- A path from the root expression to a finding, recorded as a sequence of steps. -/
abbrev ExprPath := Array ExprStep

instance : ToString ExprStep where
  toString
    | .appFn        => "appFn"
    | .appArg       => "appArg"
    | .lamType      => "lamType"
    | .lamBody      => "lamBody"
    | .forallType   => "forallType"
    | .forallBody   => "forallBody"
    | .letType      => "letType"
    | .letVal       => "letVal"
    | .letBody      => "letBody"
    | .mdata        => "mdata"
    | .proj         => "proj"
    | .constDef n   => s!"constDef {n}"
    | .constType n  => s!"constType {n}"

def ExprPath.toString (path : ExprPath) : String :=
  "[" ++ ", ".intercalate (path.toList.map ToString.toString) ++ "]"

instance : ToString ExprPath := ⟨ExprPath.toString⟩

/-- Source location of a constant's declaration. -/
structure SourceLocation where
  /-- Module (e.g. `Init.Prelude`, `MyLeanTermAuditor.Types`). -/
  module   : Name
  /-- Line and column of the declaration, if available. -/
  range?   : Option DeclarationRange := none
  deriving Repr, Inhabited

instance : ToString SourceLocation where
  toString loc :=
    let rangeStr := match loc.range? with
      | some r => s!":{r.pos.line}:{r.pos.column}"
      | none => ""
    s!"{loc.module}{rangeStr}"

-- ============================================================================
-- Extern symbol provenance
-- ============================================================================

/-- Where an extern symbol's implementation comes from. -/
inductive SymbolProvenance where
  /-- Traced through .a.trace → .o.trace → .c source file on disk. Full trust chain. -/
  | tracedToSource (cFile : String) (oFile : String) (aFile : String)
  /-- Found in the Lean toolchain runtime library (libleanrt.a). Known quantity. -/
  | toolchainRuntime (lib : String)
  /-- static inline in lean.h — no link symbol, inlined at compile time. -/
  | toolchainHeader
  -- TODO: 'binaryOnly' edge case is in review, this is placeholder
  -- /-- Found in a .a file but couldn't trace back to C source. Binary blob — sus. -/
  -- | binaryOnly (lib : String)
  /-- Symbol not found anywhere through conventional Lake build chain. Sus. -/
  | unresolved
  deriving Repr, BEq, Inhabited

-- ============================================================================
-- C type compatibility check result
-- ============================================================================

/-- Result of C type compatibility check for extern symbols. -/
inductive CTypeCheckResult where
  | compatible (line : Nat := 0)        -- C types match Lean declaration; line in C source
  | mismatch (details : String) (line : Nat := 0) -- types don't match — CRITICAL finding
  | unparseable (reason : String)       -- couldn't parse C source — SUS
  | notChecked                          -- no C source to check (toolchain/unresolved)
  deriving Repr, BEq, Inhabited

instance : ToString CTypeCheckResult where
  toString
    | .compatible _    => "compatible"
    | .mismatch d _    => s!"MISMATCH: {d}"
    | .unparseable r   => s!"UNPARSEABLE: {r}"
    | .notChecked      => "not-checked"

-- ============================================================================
-- First pass: fast classification (no paths)
-- ============================================================================

/-- Summary info about a finding constant, collected during the first (fast) pass.
    No paths stored — just classification, reachability flags, and source location. -/
structure FindingInfo where
  /-- The constant's name. -/
  name              : Name
  /-- The constant's classification (axiom, opaque, or extern). -/
  finding           : Finding
  /-- The constant's declared (polymorphic) type — e.g. `Array α → Nat` for `Array.size`. -/
  type              : Expr := .sort .zero
  /-- Pretty-printed type string, filled by `resolveLocations`. Empty until then. -/
  typeStr           : String := ""
  /-- Where this constant is declared (module + source range). -/
  location          : SourceLocation
  /-- Reached through at least one runtime (non-proof) path? -/
  reachableAtRuntime : Bool := false
  /-- Reached through at least one proof-term path? -/
  reachableInProof   : Bool := false
  /-- How many times this constant was encountered during traversal. -/
  numEncounters      : Nat := 0
  /-- Where the extern symbol's native implementation lives, filled by `resolveProvenance`. -/
  provenance?        : Option SymbolProvenance := none
  /-- Result of C type compatibility check, filled by `resolveTypeAudit`. -/
  typeCheck          : CTypeCheckResult := .notChecked
  deriving Inhabited

/-- The result of the first (fast) audit pass.
    - `findings`: constants with a finding (axiom/opaque/extern), with flags.
    - `visited`: all constants whose bodies have been traversed (for dedup).
    - `reverseDeps`: for each constant C, the set of constants whose body/type references C. -/
structure AuditResult where
  /-- Constants with findings — classification + reachability flags. -/
  findings    : NameMap FindingInfo := ∅
  /-- All constants whose bodies have been traversed (finding or not). -/
  visited     : Lean.NameHashSet := {}
  /-- Reverse dependency graph: child → {parents that reference child}. -/
  reverseDeps : NameMap Lean.NameHashSet := ∅
  deriving Inhabited

/-- All findings as an array. -/
def AuditResult.findingsArray (r : AuditResult) : Array FindingInfo :=
  r.findings.foldl (init := #[]) fun acc _ fi => acc.push fi

/-- Number of constants visited (including non-finding ones). -/
def AuditResult.numVisited (r : AuditResult) : Nat :=
  r.visited.size

/-- Number of constants with findings. -/
def AuditResult.numFindings (r : AuditResult) : Nat :=
  r.findings.size

-- ============================================================================
-- Second pass: constant-chain queries (pure DAG traversal)
-- ============================================================================

/-- Result of a "which children of `from` lead to `target`?" query. -/
structure DrillResult where
  /-- The constant we're drilling from. -/
  from_   : Name
  /-- The target we're looking for downstream. -/
  target  : Name
  /-- Direct dependencies of `from_` that transitively reach `target`. -/
  children : List Name := []
  deriving Inhabited

instance : ToString DrillResult where
  toString dr :=
    let childStr := ", ".intercalate (dr.children.map Name.toString)
    s!"{dr.from_} → [{childStr}] → ... → {dr.target}"

-- ============================================================================
-- Shared types
-- ============================================================================

/-- Is this constant a theorem? -/
def isTheorem (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ => true
  | _          => false

/-- Context available when deciding whether to recurse into or report a constant
    during the first pass. Lightweight — no ExprPath, just a depth counter and
    the chain of constants on the current traversal stack. -/
structure ConstContext where
  env         : Environment
  name        : Name
  ci          : ConstantInfo
  levels      : List Level
  finding     : Option Finding
  /-- `true` if we're currently inside a theorem's value (proof territory). -/
  inProofTerm : Bool
  /-- Number of constant boundaries crossed from the root to here. -/
  depth       : Nat
  /-- Chain of constant names on the current traversal stack (most recent last). -/
  constStack  : Array Name

/-- Context available when deciding whether to descend into a structural
    subexpression (appFn, appArg, lamBody, forallType, etc.). -/
structure DescendContext where
  step          : ExprStep
  /-- The constant whose body we're currently traversing, if any. -/
  currentConst? : Option (Name × ConstantInfo)
  inProofTerm   : Bool

/-- Configuration for the auditor.
    Three predicates control traversal at different granularities:
    - `shouldRecurse`: at constant boundaries — enter this constant's type/value?
    - `shouldReport`: at constant boundaries — include this in the output?
    - `shouldDescend`: at structural positions — recurse into this subexpression?

    The `drill` and `drillDepth` fields control the second-pass drill-down query.
    These are ignored by the pure traversal functions and only consumed by the
    `#audit` command / `AuditM` pipeline. -/
structure AuditConfig where
  /-- Should we recurse into this constant's definition/type? -/
  shouldRecurse : ConstContext → Bool := fun _ => true
  /-- Should we report this constant if it's interesting? -/
  shouldReport  : ConstContext → Bool := fun _ => true
  /-- Should we descend into this structural subexpression? -/
  shouldDescend : DescendContext → Bool := fun _ => true
  /-- Drill-down targets: for each name, show which direct dependencies of
      the audited constant(s) transitively reach it. Empty list means no drill. -/
  drill         : List Name := []

/-- Default config: recurse everywhere, report everything, descend into all subexpressions. -/
def AuditConfig.default : AuditConfig := {}

-- ============================================================================
-- Serializable types for JSON round-tripping
-- ============================================================================

/-- Serializable version of SymbolProvenance. -/
inductive SymbolProvenanceSer where
  | tracedToSource (cFile : String) (oFile : String) (aFile : String)
  | toolchainRuntime (lib : String)
  | toolchainHeader
  -- TODO: 'binaryOnly' edge case is in review, this is placeholder
  -- | binaryOnly (lib : String)
  | unresolved
  deriving Repr, ToJson, FromJson

/-- Serializable version of CTypeCheckResult. -/
inductive CTypeCheckResultSer where
  | compatible (line : Nat := 0)
  | mismatch (details : String) (line : Nat := 0)
  | unparseable (reason : String)
  | notChecked
  deriving Repr, ToJson, FromJson

def CTypeCheckResult.serialize : CTypeCheckResult → CTypeCheckResultSer
  | .compatible l    => .compatible l
  | .mismatch d l    => .mismatch d l
  | .unparseable r => .unparseable r
  | .notChecked    => .notChecked

def SymbolProvenance.serialize : SymbolProvenance → SymbolProvenanceSer
  | .tracedToSource c o a => .tracedToSource c o a
  | .toolchainRuntime l => .toolchainRuntime l
  | .toolchainHeader => .toolchainHeader
  -- TODO: 'binaryOnly' edge case is in review, this is placeholder
  -- | .binaryOnly l => .binaryOnly l
  | .unresolved => .unresolved

/-- Serializable version of `FindingInfo`. Replaces `Expr` with its pretty-printed
    string and `SourceLocation` with its string representation. -/
structure FindingInfoSer where
  name              : Name
  finding           : Finding
  type              : String
  location          : String
  reachableAtRuntime : Bool
  reachableInProof   : Bool
  numEncounters      : Nat
  provenance?        : Option SymbolProvenanceSer := none
  typeCheck          : CTypeCheckResultSer := .notChecked
  deriving ToJson, FromJson

/-- Serializable version of `DrillResult`. -/
structure DrillResultSer where
  from_    : Name
  target   : Name
  children : Array Name
  deriving ToJson, FromJson

/-- Serializable version of the full audit output. -/
structure AuditResultSer where
  audited  : Array Name
  visited  : Nat
  findings : Array FindingInfoSer
  drill    : Array DrillResultSer
  deriving ToJson, FromJson

def FindingInfo.serialize (fi : FindingInfo) : FindingInfoSer := {
  name              := fi.name
  finding           := fi.finding
  type              := if fi.typeStr.isEmpty then "unknown" else fi.typeStr
  location          := toString fi.location
  reachableAtRuntime := fi.reachableAtRuntime
  reachableInProof   := fi.reachableInProof
  numEncounters      := fi.numEncounters
  provenance?        := fi.provenance?.map SymbolProvenance.serialize
  typeCheck          := fi.typeCheck.serialize
}

def DrillResult.serialize (dr : DrillResult) : DrillResultSer := {
  from_    := dr.from_
  target   := dr.target
  children := dr.children.toArray
}

def AuditResult.serialize (result : AuditResult) (names : Array Name)
    (drills : Array DrillResult := #[]) : AuditResultSer := {
  audited  := names
  visited  := result.numVisited
  findings := result.findingsArray.map FindingInfo.serialize
  drill    := drills.map DrillResult.serialize
}

end MyLeanTermAuditor
