import Def.Data.List.Slice
import Def.Data.List.List
open Lean


class IsConstant (T : Type v) where
  is_constant : T → Prop

