import Def.Data.List.Slice
import Syntax.Data.List.List.Part5
open Lean


macro_rules
  | `($x[:$stop :$step]) => `(($x).getSlice ⟨(if $step < 0 then -1 else 0 : ℤ), ($stop : ℤ), ($step : ℤ)⟩)

