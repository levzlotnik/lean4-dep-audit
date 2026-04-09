import Lean
open Lean

-- Explore: what's available for extern?
#check @Lean.isExtern            -- env → name → Bool?
#check @ExternEntry
#check @Lean.getExternAttrData?

-- Explore: Name prefix checking
#check @Lean.Name.isPrefixOf
#check @Lean.Name.components
