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
  name     : Name
  finding  : Finding
  path     : ExprPath := #[]
  deriving Repr, Inhabited

/-- The result of an audit: all interesting constants found. -/
structure AuditResult where
  entries : Array AuditEntry := #[]
  /-- All constants we visited (for diagnostics). -/
  visited : Lean.NameHashSet := {}
  deriving Inhabited

/-- Configuration for the auditor. -/
structure AuditConfig where
  /-- Should we recurse into this constant's definition? -/
  shouldRecurse : Name → Bool := fun _ => true
  /-- Should we report this constant if it's interesting? -/
  shouldReport  : Name → Bool := fun _ => true

/-- Default config: recurse everywhere, report everything. -/
def AuditConfig.default : AuditConfig := {}

/-- Config that skips recursing into trusted namespaces but still reports
    interesting things found at the boundary. -/
def AuditConfig.trustPrefixes (prefixes : List Name) : AuditConfig where
  shouldRecurse := fun n => !prefixes.any (Name.isPrefixOf · n)
  shouldReport  := fun _ => true

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

/-- Core auditor: walk an `Expr`, collect interesting constants.
    The `path` parameter tracks the traversal route from the root to each finding. -/
partial def auditExpr (env : Environment) (config : AuditConfig) (e : Expr)
    (path : ExprPath) (state : AuditResult) : AuditResult :=
  go e path state
where
  go (e : Expr) (path : ExprPath) (s : AuditResult) : AuditResult :=
    match e with
    | .const name _ =>
      if s.visited.contains name then s
      else
        let s := { s with visited := s.visited.insert name }
        match env.find? name with
        | some ci =>
          -- Classify and maybe report
          let s := if config.shouldReport name then
            match classifyConst env ci with
            | some f => { s with entries := s.entries.push { name, finding := f, path } }
            | none   => s
          else s
          -- Recurse into the constant's type and value if config allows
          if config.shouldRecurse name then
            let s := go ci.type (path.push (.constType name)) s
            match ci.value? with
            | some v => go v (path.push (.constDef name)) s
            | none   => s
          else s
        | none => s
    | .app fn arg           => go arg (path.push .appArg) (go fn (path.push .appFn) s)
    | .lam _ ty body _      => go body (path.push .lamBody) (go ty (path.push .lamType) s)
    | .forallE _ ty body _  => go body (path.push .forallBody) (go ty (path.push .forallType) s)
    | .letE _ ty val body _ =>
        go body (path.push .letBody) (go val (path.push .letVal) (go ty (path.push .letType) s))
    | .mdata _ expr         => go expr (path.push .mdata) s
    | .proj _ _ expr        => go expr (path.push .proj) s
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => s

/-- Run the auditor on a named constant from the environment. -/
def auditConst (env : Environment) (config : AuditConfig) (name : Name) : AuditResult :=
  let empty : AuditResult := { entries := #[], visited := {} }
  match env.find? name with
  | some ci =>
    let s := auditExpr env config ci.type #[.constType name] empty
    match ci.value? with
    | some v => auditExpr env config v #[.constDef name] s
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

end MyLeanTermAuditor
