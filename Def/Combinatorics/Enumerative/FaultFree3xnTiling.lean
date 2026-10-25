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
import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling


namespace MetaMathlibExt

/-- Two cells share an edge. -/
def TilingCell.Adjacent {n : ℕ} (x y : TilingCell n) : Prop :=
  (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
    (x.2 = y.2 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val))

/-- A tile is either one unit square or one domino joining adjacent cells. -/
def IsSquareOrDomino {n : ℕ} (d : Finset (TilingCell n)) : Prop :=
  d.card = 1 ∨
    (d.card = 2 ∧ ∀ x ∈ d, ∀ y ∈ d, x ≠ y → TilingCell.Adjacent x y)

end MetaMathlibExt
