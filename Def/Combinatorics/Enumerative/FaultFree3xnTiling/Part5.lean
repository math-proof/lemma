/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part3

@[expose] public section

namespace MetaMathlibExt

def ff3EdgeDomino {n : ℕ} : ff3Edge n → Finset (TilingCell (n + 1))
  | Sum.inl e => ff3HorizontalDomino e.1 e.2
  | Sum.inr e => ff3VerticalDomino e.1 e.2

end MetaMathlibExt
