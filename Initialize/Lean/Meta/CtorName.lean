module

public import Lean
public import Def.Lean.Meta.CtorName
public section

open Lean Elab Command Parser.Term

export CtorName (ctorName)


initialize
  registerDerivingHandler ``CtorName fun indNames => do
    indNames.forM mkCtorName
    return true
