import Lean
import Class.Lean.Meta.CtorName
open Lean Elab Command Parser.Term

export CtorName (ctorName)


def mkCtorName (indName : Name) : CommandElabM Unit := do
  elabCommand <| ← `(
instance : CtorName $(mkIdent indName) where
  ctorName := fun $(← (← getConstInfoInduct indName).ctors.toArray.mapM fun ctor => do
    let val := ctor.getString!
    `(matchAltExpr| | .$(mkIdent val.toName):ident $(List.replicate (← getConstInfoCtor ctor).numFields (← `(_)) |>.toArray)* => $(Syntax.mkStrLit val))
  ):matchAlt*

def $(mkIdent (indName.str "ctorName")) : $(mkIdent indName) → String := CtorName.ctorName
)
