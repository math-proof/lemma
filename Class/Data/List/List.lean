module

public import Def.Data.List.Slice
public import Def.Data.List.List
public section

open Lean


class IsConstant (T : Type v) where
  is_constant : T → Prop

