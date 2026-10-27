import Def.Data.List.Slice
import Syntax.Data.List.List.Part4
open Lean


macro_rules
  | `($x[$start :$stop]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), (1 : ℤ)⟩)
  | `($x[$start :$stop :]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), (1 : ℤ)⟩)

