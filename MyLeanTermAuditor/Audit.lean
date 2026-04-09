import Lean

open Lean

namespace MyLeanTermAuditor

/-- Classification of a constant that we consider "interesting" for audit purposes. -/
inductive Finding where
  | axiom_    : Finding
  | opaque_   : Finding
  | extern_   (sym : String) : Finding
  deriving Repr, BEq, Inhabited

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

/-- A single audit entry: the constant name, where it lives, and what kind it is. -/
structure AuditEntry where
  name        : Name
  finding     : Finding
  path        : ExprPath := #[]
  /-- `true` if this finding was reached through a proof (theorem) term.
      These are kernel-time dependencies, not runtime dependencies. -/
  inProofTerm : Bool := false
  deriving Repr, Inhabited

/-- The result of an audit: all interesting constants found. -/
structure AuditResult where
  entries : Array AuditEntry := #[]
  /-- All constants we visited (for diagnostics). -/
  visited : Lean.NameHashSet := {}
  deriving Inhabited

-- ============================================================================
-- Predicate contexts: rich information available at decision points
-- ============================================================================

/-- Is this constant a theorem? -/
def isTheorem (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ => true
  | _          => false

/-- Context available when deciding whether to recurse into or report a constant.
    Built once per `.const name levels` hit during traversal. -/
structure ConstContext where
  env         : Environment
  name        : Name
  ci          : ConstantInfo
  path        : ExprPath
  levels      : List Level
  finding     : Option Finding
  /-- `true` if we're currently inside a theorem's value (proof territory). -/
  inProofTerm : Bool

/-- Context available when deciding whether to descend into a structural
    subexpression (appFn, appArg, lamBody, forallType, etc.). -/
structure DescendContext where
  step          : ExprStep
  path          : ExprPath
  /-- The constant whose body we're currently traversing, if any. -/
  currentConst? : Option (Name × ConstantInfo)
  inProofTerm   : Bool

/-- Configuration for the auditor.
    Three predicates control traversal at different granularities:
    - `shouldRecurse`: at constant boundaries — enter this constant's type/value?
    - `shouldReport`: at constant boundaries — include this in the output?
    - `shouldDescend`: at structural positions — recurse into this subexpression? -/
structure AuditConfig where
  /-- Should we recurse into this constant's definition/type? -/
  shouldRecurse : ConstContext → Bool := fun _ => true
  /-- Should we report this constant if it's interesting? -/
  shouldReport  : ConstContext → Bool := fun _ => true
  /-- Should we descend into this structural subexpression? -/
  shouldDescend : DescendContext → Bool := fun _ => true

/-- Default config: recurse everywhere, report everything, descend into all subexpressions. -/
def AuditConfig.default : AuditConfig := {}

/-- Get the extern symbol name for a constant, if it has one. -/
def getExternSymbol? (env : Environment) (name : Name) : Option String :=
  match Lean.getExternAttrData? env name with
  | some data =>
    -- Find the first entry with a symbol name
    match data.entries.find? fun e => match e with
      | .standard _ _ => true
      | .inline _ _   => true
      | _             => false
    with
    | some (.standard _ s) => some s
    | some (.inline _ s)   => some s
    | _                    => some "<adhoc/opaque extern>"
  | none => none

/-- Classify a constant as interesting or not. Returns `none` if not interesting. -/
def classifyConst (env : Environment) (ci : ConstantInfo) : Option Finding :=
  match ci with
  | .axiomInfo _  => some .axiom_
  | .opaqueInfo _ => some .opaque_
  | _ =>
    match getExternSymbol? env ci.name with
    | some sym => some (.extern_ sym)
    | none     => none

/-- Internal traversal state threaded through the recursive walk. -/
structure TraversalState where
  /-- The constant whose body we're currently inside (for DescendContext). -/
  currentConst? : Option (Name × ConstantInfo) := none
  /-- Are we inside a proof term (theorem value)? -/
  inProofTerm   : Bool := false
  deriving Inhabited

/-- Core auditor: walk an `Expr`, collect interesting constants.
    The `path` parameter tracks the traversal route from the root to each finding.
    The `ts` parameter carries traversal state (current constant, proof term flag). -/
partial def auditExpr (env : Environment) (config : AuditConfig) (e : Expr)
    (path : ExprPath) (ts : TraversalState) (state : AuditResult) : AuditResult :=
  go e path ts state
where
  /-- Try to descend into a subexpression, checking `shouldDescend` first. -/
  descend (e : Expr) (step : ExprStep) (path : ExprPath) (ts : TraversalState)
      (s : AuditResult) : AuditResult :=
    let dctx : DescendContext := {
      step          := step
      path          := path
      currentConst? := ts.currentConst?
      inProofTerm   := ts.inProofTerm
    }
    if config.shouldDescend dctx then
      go e (path.push step) ts s
    else s
  go (e : Expr) (path : ExprPath) (ts : TraversalState) (s : AuditResult) : AuditResult :=
    match e with
    | .const name levels =>
      if s.visited.contains name then s
      else
        let s := { s with visited := s.visited.insert name }
        match env.find? name with
        | some ci =>
          let finding := classifyConst env ci
          let cctx : ConstContext := {
            env, name, ci, path, levels, finding
            inProofTerm := ts.inProofTerm
          }
          -- Classify and maybe report
          let s := if config.shouldReport cctx then
            match finding with
            | some f =>
              let entry : AuditEntry := { name, finding := f, path, inProofTerm := ts.inProofTerm }
              { s with entries := s.entries.push entry }
            | none   => s
          else s
          -- Recurse into the constant's type and value if config allows
          if config.shouldRecurse cctx then
            -- Update traversal state: entering this constant
            let tsType : TraversalState := {
              currentConst? := some (name, ci)
              inProofTerm := ts.inProofTerm
            }
            let s := go ci.type (path.push (.constType name)) tsType s
            match ci.value? with
            | some v =>
              -- Entering a theorem's value flips inProofTerm to true
              let inProof := ts.inProofTerm || isTheorem ci
              let tsDef : TraversalState := {
                currentConst? := some (name, ci)
                inProofTerm := inProof
              }
              go v (path.push (.constDef name)) tsDef s
            | none   => s
          else s
        | none => s
    | .app fn arg =>
        let s := descend fn .appFn path ts s
        descend arg .appArg path ts s
    | .lam _ ty body _ =>
        let s := descend ty .lamType path ts s
        descend body .lamBody path ts s
    | .forallE _ ty body _ =>
        let s := descend ty .forallType path ts s
        descend body .forallBody path ts s
    | .letE _ ty val body _ =>
        let s := descend ty .letType path ts s
        let s := descend val .letVal path ts s
        descend body .letBody path ts s
    | .mdata _ expr => descend expr .mdata path ts s
    | .proj _ _ expr => descend expr .proj path ts s
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => s

/-- Run the auditor on a named constant from the environment. -/
def auditConst (env : Environment) (config : AuditConfig) (name : Name) : AuditResult :=
  let empty : AuditResult := { entries := #[], visited := {} }
  match env.find? name with
  | some ci =>
    let tsType : TraversalState := { currentConst? := some (name, ci) }
    let s := auditExpr env config ci.type #[.constType name] tsType empty
    match ci.value? with
    | some v =>
      let tsDef : TraversalState := {
        currentConst? := some (name, ci)
        inProofTerm := isTheorem ci
      }
      auditExpr env config v #[.constDef name] tsDef s
    | none   => s
  | none => empty

-- ============================================================================
-- Compile-time stack trace: post-processing on ExprPath
-- ============================================================================

/-- Whether an ExprStep enters a named constant (the "stack frames"). -/
def ExprStep.constName? : ExprStep → Option (Name × Bool)
  | .constDef n  => some (n, true)   -- true = entered definition
  | .constType n => some (n, false)  -- false = entered type
  | _            => none

/-- A single frame in the compile-time stack trace.
    Each frame represents entering a named constant's definition or type,
    with the structural steps taken *within* that constant to reach the next frame. -/
structure StackFrame where
  /-- The constant whose definition/type we entered. -/
  name      : Name
  /-- `true` if we entered the definition (value), `false` if the type. -/
  isDef     : Bool
  /-- Structural steps within this constant's body before hitting the next constant. -/
  localSteps : Array ExprStep := #[]
  deriving Repr, Inhabited

instance : ToString StackFrame where
  toString f :=
    let kind := if f.isDef then "def" else "type"
    let detail := if f.localSteps.isEmpty then ""
      else
        let steps := ", ".intercalate (f.localSteps.toList.map ToString.toString)
        s!" [{steps}]"
    s!"{f.name} ({kind}){detail}"

/-- Extract the constant chain ("stack frames") from a raw ExprPath.
    Groups the path into frames: each constDef/constType starts a new frame,
    and the structural steps between frames are collected as `localSteps`. -/
def ExprPath.toFrames (path : ExprPath) : Array StackFrame :=
  let (frames, pending) := path.foldl (init := (#[], none))
    fun (frames, current?) step =>
      match step.constName? with
      | some (name, isDef) =>
        -- New constant frame — flush the previous one if any
        let frames := match current? with
          | some frame => frames.push frame
          | none       => frames
        (frames, some { name, isDef, localSteps := #[] : StackFrame })
      | none =>
        -- Structural step — append to current frame
        let current? := current?.map fun frame =>
          { frame with localSteps := frame.localSteps.push step }
        (frames, current?)
  -- Flush the last frame
  match pending with
  | some frame => frames.push frame
  | none       => frames

/-- Pretty-print an ExprPath as a compile-time stack trace.
    Shows the chain of constants traversed, like a call stack.

    Example output:
    ```
      myMain (def)
        → Bind.bind (def)
        → Pure.pure (def)
        → Decidable.em (def)
        → propext
    ``` -/
def ExprPath.toStackTrace (path : ExprPath) (findingName : Name) (indent : String := "    ")
    : String :=
  let frames := path.toFrames
  let lines := frames.toList.map fun f =>
    let kind := if f.isDef then "def" else "type"
    s!"{indent}→ {f.name} ({kind})"
  let traceLines := "\n".intercalate lines
  let last := s!"{indent}→ {findingName}"
  if traceLines.isEmpty then last
  else s!"{traceLines}\n{last}"

/-- Compact stack trace: only show the constant chain, no structural detail.
    Renders as a single line: `myMain → Bind.bind → ... → propext` -/
def ExprPath.toCompactTrace (path : ExprPath) (findingName : Name) : String :=
  let frames := path.toFrames
  let names := frames.toList.map fun f => Name.toString f.name
  let chain := names ++ [Name.toString findingName]
  " → ".intercalate chain

-- ============================================================================
-- Filter combinators: composable predicates for AuditConfig
-- ============================================================================

namespace Filter

/-- Filter by constant name. -/
def byName (p : Name → Bool) : ConstContext → Bool :=
  fun ctx => p ctx.name

/-- Filter: constant is in one of the given namespaces. -/
def inNamespaces (ns : List Name) : ConstContext → Bool :=
  fun ctx => ns.any (Name.isPrefixOf · ctx.name)

/-- Filter: constant is NOT in any of the given namespaces. -/
def notInNamespaces (ns : List Name) : ConstContext → Bool :=
  fun ctx => !ns.any (Name.isPrefixOf · ctx.name)

/-- Filter: only axioms. -/
def axiomsOnly : ConstContext → Bool :=
  fun ctx => ctx.finding == some Finding.axiom_

/-- Filter: only opaques. -/
def opaquesOnly : ConstContext → Bool :=
  fun ctx => ctx.finding == some Finding.opaque_

/-- Filter: only externs. -/
def externsOnly : ConstContext → Bool :=
  fun ctx => match ctx.finding with | some (Finding.extern_ _) => true | _ => false

/-- Filter: only findings reachable through runtime code (not proof terms).
    These are the externs/axioms your compiled binary actually depends on. -/
def runtimeOnly : ConstContext → Bool :=
  fun ctx => !ctx.inProofTerm

/-- Filter: only findings reachable through proof terms (kernel-time dependencies).
    These are externs/axioms the kernel evaluates during type-checking. -/
def kernelOnly : ConstContext → Bool :=
  fun ctx => ctx.inProofTerm

/-- Filter: constant chain depth (number of constDef/constType frames) ≤ n. -/
def maxDepth (n : Nat) : ConstContext → Bool :=
  fun ctx =>
    let depth := ctx.path.foldl (init := 0) fun acc step =>
      match step.constName? with | some _ => acc + 1 | none => acc
    depth ≤ n

/-- Filter: the path passes through a specific constant. -/
def pathThrough (target : Name) : ConstContext → Bool :=
  fun ctx => ctx.path.any fun step =>
    match step.constName? with
    | some (n, _) => n == target
    | none => false

/-- Filter: has a finding (is interesting). Useful for `shouldReport` —
    even with the default, `shouldReport` only fires on classified constants,
    but this makes it explicit. -/
def hasAnyFinding : ConstContext → Bool :=
  fun ctx => ctx.finding.isSome

/-- Combinator: logical AND of two predicates. -/
def «and» (f g : ConstContext → Bool) : ConstContext → Bool :=
  fun ctx => f ctx && g ctx

/-- Combinator: logical OR of two predicates. -/
def «or» (f g : ConstContext → Bool) : ConstContext → Bool :=
  fun ctx => f ctx || g ctx

/-- Combinator: logical NOT of a predicate. -/
def «not» (f : ConstContext → Bool) : ConstContext → Bool :=
  fun ctx => !f ctx

end Filter

namespace Descend

/-- Descend: skip proof terms entirely. When we're inside a theorem's value,
    don't descend into any structural subexpressions.
    This prunes the entire Lean.Omega / proof-checking subtree. -/
def skipProofTerms : DescendContext → Bool :=
  fun ctx => !ctx.inProofTerm

/-- Descend: skip type positions (forallType, lamType, letType).
    Keeps only computational content — bodies and values. -/
def skipTypes : DescendContext → Bool :=
  fun ctx => match ctx.step with
    | .forallType | .lamType | .letType => false
    | _ => true

/-- Descend: go everywhere (default behavior). -/
def all : DescendContext → Bool :=
  fun _ => true

/-- Combinator: logical AND of two descent predicates. -/
def «and» (f g : DescendContext → Bool) : DescendContext → Bool :=
  fun ctx => f ctx && g ctx

/-- Combinator: logical OR of two descent predicates. -/
def «or» (f g : DescendContext → Bool) : DescendContext → Bool :=
  fun ctx => f ctx || g ctx

end Descend

-- ============================================================================
-- Convenience config constructors
-- ============================================================================

/-- Config that skips recursing into trusted namespaces but still reports
    interesting things found at the boundary. -/
def AuditConfig.trustPrefixes (prefixes : List Name) : AuditConfig where
  shouldRecurse := Filter.notInNamespaces prefixes
  shouldReport  := fun _ => true

/-- Config: only report runtime dependencies (skip proof-term findings). -/
def AuditConfig.runtimeOnly : AuditConfig where
  shouldReport  := Filter.runtimeOnly
  shouldDescend := Descend.skipProofTerms

/-- Config: only report externs reachable through runtime code. -/
def AuditConfig.runtimeExterns : AuditConfig where
  shouldReport  := Filter.and Filter.externsOnly Filter.runtimeOnly
  shouldDescend := Descend.skipProofTerms

/-- Config: only report axioms (full traversal including proofs). -/
def AuditConfig.axiomsOnly : AuditConfig where
  shouldReport := Filter.axiomsOnly

end MyLeanTermAuditor
