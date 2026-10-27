import Def.Data.List.Slice
import Syntax.Data.List.List.Part7
open Lean


macro_rules
  | `($x[$start :$stop :$step]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), ($step : ℤ)⟩)

