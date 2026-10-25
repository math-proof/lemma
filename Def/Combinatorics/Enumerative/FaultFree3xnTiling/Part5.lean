/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part3


namespace MetaMathlibExt

def ff3EdgeDomino {n : ℕ} : ff3Edge n → Finset (TilingCell (n + 1))
  | Sum.inl e => ff3HorizontalDomino e.1 e.2
  | Sum.inr e => ff3VerticalDomino e.1 e.2

end MetaMathlibExt
