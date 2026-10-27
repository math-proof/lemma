import Def.Data.List.Slice
import Class.Data.List.List
open Lean


/--
Define the postfix operator using the type class
-/
macro x:term:min "is" "constant" : term =>
  `(IsConstant.is_constant $x)

