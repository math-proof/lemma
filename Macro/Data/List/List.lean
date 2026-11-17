module

public import Def.Data.List.Slice
public import Class.Data.List.List

public meta section

open Lean


/--
Define the postfix operator using the type class
-/
macro x:term:min "is" "constant" : term =>
  `(IsConstant.is_constant $x)
