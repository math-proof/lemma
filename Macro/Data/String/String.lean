import Batteries.Data.String
import Lean.Meta
import Def.Lean.Char
import Def.Data.String.String
open Lean.Meta
open Lean (Json JsonNumber)


macro fmt:str ".format" args:term,+ : term => do
  `($(fmt).printf [$(← args.getElems.mapM fun arg => `(toString $arg)),*])


