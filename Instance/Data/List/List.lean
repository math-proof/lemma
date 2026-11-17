module

public import Def.Data.List.Slice
public import Macro.Data.List.List

@[expose] public section

open Lean


instance : IsConstant (List α) where
  is_constant : List α → Prop
    | [] => True
    | (x0 :: X) => ∀ x ∈ X, x = x0

