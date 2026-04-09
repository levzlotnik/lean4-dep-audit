import Lean
import MyLeanTermAuditor.Types

open Lean

namespace MyLeanTermAuditor

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

end MyLeanTermAuditor
