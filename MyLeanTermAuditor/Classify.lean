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

/-- Classify the kind of an opaque constant. -/
def classifyOpaqueKind (env : Environment) (info : OpaqueVal) : OpaqueKind :=
  if Lean.hasInitAttr env info.name
      || Lean.isIOUnitInitFn env info.name
      || Lean.isIOUnitBuiltinInitFn env info.name then
    .initialize_
  else if info.value.isAppOfArity ``default 2 then
    -- Body is literally `@default T inst` — a NonemptyType implementation
    -- or `implemented_by` target. Not a partial def.
    .implementedBy_
  else
    -- Has an actual body (lambdas, lets, etc.) — partial def.
    .partial_

/-- Classify a constant as interesting or not. Returns `none` if not interesting. -/
def classifyConst (env : Environment) (ci : ConstantInfo) : Option Finding :=
  -- Externs take priority: an extern opaque should be classified as extern, not opaque.
  match getExternSymbol? env ci.name with
  | some sym => some (.extern_ sym)
  | none =>
    match ci with
    | .axiomInfo _     => some .axiom_
    | .opaqueInfo info => some (.opaque_ (classifyOpaqueKind env info))
    | _                => none

end MyLeanTermAuditor
