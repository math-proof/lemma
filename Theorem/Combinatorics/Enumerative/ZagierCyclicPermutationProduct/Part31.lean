/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part28
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagFullSlice_of_terminal {n : ℕ} (p : ZagPointedPlane n)
    (q : ZagMarkedPlane n) (h : zagSliceStep p = Sum.inl q) :
    (zagFullSlice p).out =
      ⟨q.order, q.vertical, q.marked.first, .terminal q.marked⟩ := by
  classical
  rw [zagFullSlice.eq_1]
  by_cases hres : zagNontrivialAntiExceedance
      (zagSliceOrder p.order p.vertical p.point p.point_property)
      (zagSliceVertical p.order p.vertical p.point p.point_property) p.point
  · have h' := h
    simp only [zagSliceStep, hres, ↓reduceDIte, reduceCtorEq] at h'
  · simp only [hres, ↓reduceDIte, ZagOddMarkedPlane.mk.injEq]
    have h' := h
    simp only [zagSliceStep, hres, ↓reduceDIte, Sum.inl.injEq] at h'
    have hq := h'
    cases hq
    exact ⟨rfl, rfl, rfl, HEq.rfl⟩

theorem zagFullSlice_of_residual {n : ℕ} (p : ZagPointedPlane n)
    (q : ZagResidualMarkedPlane n) (h : zagSliceStep p = Sum.inr q) :
    let p' : ZagPointedPlane n :=
      ⟨q.order, q.vertical, q.point, q.point_property⟩
    let next := zagFullSlice p'
    (zagFullSlice p).out = {
      order := next.out.order
      vertical := next.out.vertical
      root := q.marked.first
      marks := .prepend q.marked.first q.marked.middle next.out.root
        (next.preserves_before q.marked.first
          (by
            rw [q.point_cycle_min]
            exact q.marked.first_lt_middle.trans q.marked.middle_lt_third)
          q.marked.first_mem)
        (next.preserves_before q.marked.middle
          (by rw [q.point_cycle_min]; exact q.marked.middle_lt_third)
          q.marked.middle_mem)
        q.marked.first_lt_middle
        (by rw [next.root_eq, q.point_cycle_min]; exact q.marked.middle_lt_third)
        next.out.marks
    } := by
  classical
  rw [zagFullSlice.eq_1]
  by_cases hres : zagNontrivialAntiExceedance
      (zagSliceOrder p.order p.vertical p.point p.point_property)
      (zagSliceVertical p.order p.vertical p.point p.point_property) p.point
  · simp only [hres, ↓reduceDIte, ZagOddMarkedPlane.mk.injEq]
    have h' := h
    simp only [zagSliceStep, hres, ↓reduceDIte, Sum.inr.injEq] at h'
    have hq := h'
    cases hq
    exact ⟨rfl, rfl, rfl, HEq.rfl⟩
  · have h' := h
    simp only [zagSliceStep, hres, ↓reduceDIte, reduceCtorEq] at h'

end MetaMathlibExt
