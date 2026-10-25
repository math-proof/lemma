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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part4


namespace MetaMathlibExt

def ff3EdgeDominoes {n : ℕ} (E : Finset (ff3Edge n)) :=
  E.image ff3EdgeDomino

def ff3EdgesOf {n : ℕ} (D : Finset (Finset (TilingCell (n + 1)))) :=
  Finset.univ.filter fun e ↦ ff3EdgeDomino e ∈ D

end MetaMathlibExt
