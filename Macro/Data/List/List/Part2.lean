import Def.Data.List.Slice
import Syntax.Data.List.List.Part2
open Lean


macro_rules
  | `($x[:$stop]) => `(($x).getSlice ⟨(0 : ℤ), ($stop : ℤ), (1 : ℤ)⟩)

