module

public import Batteries.Data.String
public import Lean.Meta
public import Def.Lean.Char
public import Def.Data.String.String

public meta section

open Lean.Meta
open Lean (Json JsonNumber)


macro fmt:str ".format" args:term,+ : term => do
  `($(fmt).printf [$(← args.getElems.mapM fun arg => `(toString $arg)),*])
