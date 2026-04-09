import Lean
import MyLeanTermAuditor.Types

open Lean

namespace MyLeanTermAuditor

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
