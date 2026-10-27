import Def.Data.List.Slice
import Syntax.Data.List.List.Part3
open Lean


macro_rules
  | `($x[::$step]) => `(($x).getSlice ⟨(if $step < 0 then -1 else 0 : ℤ), (if $step < 0 then -($x).length.succ else ($x).length : ℤ), ($step : ℤ)⟩)

