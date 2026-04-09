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

end MyLeanTermAuditor
