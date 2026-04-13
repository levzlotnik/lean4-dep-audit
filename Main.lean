import Lean4DepAudit.CLI

def main (args : List String) : IO UInt32 :=
  Lean4DepAudit.CLI.run args
