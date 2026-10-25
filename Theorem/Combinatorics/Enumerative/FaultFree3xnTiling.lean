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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling


namespace MetaMathlibExt

/-- A valid square-or-domino tile is exactly a singleton or an adjacent pair. -/
theorem isSquareOrDomino_iff {n : ℕ} (d : Finset (TilingCell n)) :
    IsSquareOrDomino d ↔
      (∃ x, d = {x}) ∨
        ∃ x y, x ≠ y ∧ TilingCell.Adjacent x y ∧ d = {x, y} := by
  constructor
  · rintro (h | ⟨hcard, hadj⟩)
    · exact Or.inl (Finset.card_eq_one.mp h)
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      refine Or.inr ⟨x, y, hxy, ?_, rfl⟩
      exact hadj x (by simp) y (by simp) hxy
  · rintro (⟨x, rfl⟩ | ⟨x, y, hxy, hadj, rfl⟩)
    · exact Or.inl (by simp)
    · refine Or.inr ⟨by simp [hxy], ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hadj
      · exact ff3_adjacent_comm.mp hadj
      · exact (hab rfl).elim

end MetaMathlibExt
