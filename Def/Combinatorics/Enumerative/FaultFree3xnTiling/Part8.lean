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
import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part4


namespace MetaMathlibExt

def ff3_matchingEdgeEquiv (n : ℕ) :
    ff3FaultFreeEdgeMatchings n ≃ ff3FaultFreeMatchings (n + 1) where
  toFun E := ⟨ff3EdgeDominoes E,
    (ff3_edgeDominoes_matching_iff (n := n) E.1).mpr E.property.1,
    (ff3_edgeDominoes_faultFree_iff (n := n) E.1).mpr E.property.2⟩
  invFun D := by
    let E := ff3EdgesOf D.1
    have hEq : ff3EdgeDominoes E = D.1 :=
      ff3_edgeDominoes_edgesOf D.property.1.1
    refine ⟨E, ?_, ?_⟩
    · apply (ff3_edgeDominoes_matching_iff (n := n) E).mp
      rw [hEq]
      exact D.property.1
    · apply (ff3_edgeDominoes_faultFree_iff (n := n) E).mp
      rw [hEq]
      exact D.property.2
  left_inv E := by
    apply Subtype.ext
    change ff3EdgesOf (ff3EdgeDominoes E.1) = E.1
    exact ff3_edgesOf_edgeDominoes E.1
  right_inv D := by
    apply Subtype.ext
    change ff3EdgeDominoes (ff3EdgesOf D.1) = D.1
    exact ff3_edgeDominoes_edgesOf D.property.1.1

end MetaMathlibExt
