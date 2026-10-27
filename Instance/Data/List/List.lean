import Def.Data.List.Slice
import Macro.Data.List.List
open Lean


instance : IsConstant (List α) where
  is_constant : List α → Prop
    | [] => True
    | (x0 :: X) => ∀ x ∈ X, x = x0

