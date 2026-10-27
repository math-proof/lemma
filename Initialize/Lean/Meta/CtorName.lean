import Lean
import Def.Lean.Meta.CtorName
open Lean Elab Command Parser.Term

export CtorName (ctorName)


initialize
  registerDerivingHandler ``CtorName fun indNames => do
    indNames.forM mkCtorName
    return true

