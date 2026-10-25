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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part16


namespace MetaMathlibExt

theorem ff3_mem_edgeProfile {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (r : Fin 3) (k : Fin n) :
    r ∈ ff3ProfileRows (ff3EdgeProfile E k) ↔ Sum.inl (r, k) ∈ E.1 := by
  have h := congrArg Subtype.val
    (ff3ProfileEquiv.apply_symm_apply
      ⟨ff3EdgeProfileRows E k, ff3_edgeProfileRows_nonempty E k⟩)
  rw [show ff3ProfileRows (ff3EdgeProfile E k) = ff3EdgeProfileRows E k from h]
  simp [ff3EdgeProfileRows]

theorem ff3_edge_no_both_vertical {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (j : Fin (n + 1)) :
    ¬(Sum.inr ((0 : Fin 2), j) ∈ E.1 ∧ Sum.inr ((1 : Fin 2), j) ∈ E.1) := by
  rintro ⟨h0, h1⟩
  have hne : (Sum.inr ((0 : Fin 2), j) : ff3Edge n) ≠ Sum.inr ((1 : Fin 2), j) := by
    simp
  have hd := E.property.1 _ h0 _ h1 hne
  have hm0 : ((1 : Fin 3), j) ∈ ff3EdgeDomino (Sum.inr ((0 : Fin 2), j)) := by
    simp [ff3EdgeDomino, ff3VerticalDomino]
  have hm1 : ((1 : Fin 3), j) ∈ ff3EdgeDomino (Sum.inr ((1 : Fin 2), j)) := by
    simp [ff3EdgeDomino, ff3VerticalDomino]
  exact Finset.disjoint_left.mp hd hm0 hm1

end MetaMathlibExt
