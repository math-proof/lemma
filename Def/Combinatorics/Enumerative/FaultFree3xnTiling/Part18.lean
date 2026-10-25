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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part13


namespace MetaMathlibExt

noncomputable def ff3EdgeFilling {n : ℕ} (E : ff3FaultFreeEdgeMatchings n)
    (j : Fin (n + 1)) :
    ff3ColumnFilling (ff3Incoming ∅ (ff3EdgeProfile E) j)
      (ff3Outgoing (ff3EdgeProfile E) j) := by
  refine ⟨ff3EdgeVertical E j, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro r hin hout
    simp only [ff3Incoming] at hin
    split at hin
    · simp at hin
    · rename_i hj0
      simp only [ff3Outgoing] at hout
      split at hout
      · rename_i hjn
        let l : Fin n := ⟨j.val - 1, by omega⟩
        let k : Fin n := ⟨j.val, hjn⟩
        have hil : Sum.inl (r, l) ∈ E.1 := by
          apply (ff3_mem_edgeProfile E r l).mp
          simpa [l] using hin
        have hik : Sum.inl (r, k) ∈ E.1 := by
          apply (ff3_mem_edgeProfile E r k).mp
          simpa [k] using hout
        have hne : (Sum.inl (r, l) : ff3Edge n) ≠ Sum.inl (r, k) := by
          intro h
          injection h with h
          have := congrArg (fun e ↦ e.2.val) h
          simp [l, k] at this
          omega
        have hd := E.property.1 _ hil _ hik hne
        have hjl : l.succ = j := Fin.ext (by simp [l]; omega)
        have hjk : k.castSucc = j := Fin.ext (by simp [k])
        have hmil : (r, j) ∈ ff3EdgeDomino (Sum.inl (r, l)) := by
          simp [ff3EdgeDomino, ff3HorizontalDomino, ← hjl]
        have hmik : (r, j) ∈ ff3EdgeDomino (Sum.inl (r, k)) := by
          simp [ff3EdgeDomino, ff3HorizontalDomino, ← hjk]
        exact Finset.disjoint_left.mp hd hmil hmik
      · simp at hout
  · rw [Finset.disjoint_left]
    intro r hin hrv
    simp only [ff3Incoming] at hin
    split at hin
    · simp at hin
    · rename_i hj0
      let l : Fin n := ⟨j.val - 1, by omega⟩
      have hil : Sum.inl (r, l) ∈ E.1 := by
        apply (ff3_mem_edgeProfile E r l).mp
        simpa [l] using hin
      cases hv : ff3EdgeVertical E j with
      | none => simp [hv, ff3VerticalRows] at hrv
      | some s =>
          have his : Sum.inr (s, j) ∈ E.1 :=
            (ff3_edgeVertical_eq_some_iff E s j).mp hv
          have hd := E.property.1 _ hil _ his (by simp)
          have hjl : l.succ = j := Fin.ext (by simp [l]; omega)
          have hmil : (r, j) ∈ ff3EdgeDomino (Sum.inl (r, l)) := by
            simp [ff3EdgeDomino, ff3HorizontalDomino, ← hjl]
          have hmis : (r, j) ∈ ff3EdgeDomino (Sum.inr (s, j)) := by
            change (r, j) ∈ ff3VerticalDomino s j
            simpa [ff3VerticalDomino, ff3VerticalRows, hv] using hrv
          exact Finset.disjoint_left.mp hd hmil hmis
  · rw [Finset.disjoint_left]
    intro r hout hrv
    simp only [ff3Outgoing] at hout
    split at hout
    · rename_i hjn
      let k : Fin n := ⟨j.val, hjn⟩
      have hik : Sum.inl (r, k) ∈ E.1 := by
        apply (ff3_mem_edgeProfile E r k).mp
        simpa [k] using hout
      cases hv : ff3EdgeVertical E j with
      | none => simp [hv, ff3VerticalRows] at hrv
      | some s =>
          have his : Sum.inr (s, j) ∈ E.1 :=
            (ff3_edgeVertical_eq_some_iff E s j).mp hv
          have hd := E.property.1 _ hik _ his (by simp)
          have hjk : k.castSucc = j := Fin.ext (by simp [k])
          have hmik : (r, j) ∈ ff3EdgeDomino (Sum.inl (r, k)) := by
            simp [ff3EdgeDomino, ff3HorizontalDomino, ← hjk]
          have hmis : (r, j) ∈ ff3EdgeDomino (Sum.inr (s, j)) := by
            change (r, j) ∈ ff3VerticalDomino s j
            simpa [ff3VerticalDomino, ff3VerticalRows, hv] using hrv
          exact Finset.disjoint_left.mp hd hmik hmis
    · simp at hout

noncomputable def ff3EdgeCode {n : ℕ} (E : ff3FaultFreeEdgeMatchings n) :
    ff3Code ∅ n :=
  ⟨ff3EdgeProfile E, ff3EdgeFilling E⟩

end MetaMathlibExt
