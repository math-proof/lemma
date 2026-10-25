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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part29
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagFullMerge_terminal_out {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    (zagFullMerge ⟨e, π, m.first, .terminal m⟩).out =
      ⟨zagMergeOrder e π m, zagMergeVertical e π m,
        zagMergePoint e π m, zagMergePoint_nontrivialAntiExceedance e π m⟩ := by
  change (zagFullMergeCore e π (.terminal m)).out = _
  rw [zagFullMergeCore.eq_1]

theorem zagFullMerge_prepend_out {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (first middle third : Fin n)
    (first_mem : first ∈ zagCycleMinima e π)
    (middle_mem : middle ∈ zagCycleMinima e π)
    (first_lt_middle : first < middle) (middle_lt_third : middle < third)
    (tail : ZagOddMarks e π third) :
    let next := zagFullMerge ⟨e, π, third, tail⟩
    let m : ZagMarkedTriple next.out.order next.out.vertical := {
      first := first
      middle := middle
      third := third
      first_mem := next.preserves_before first
        (first_lt_middle.trans middle_lt_third) first_mem
      middle_mem := next.preserves_before middle middle_lt_third middle_mem
      third_mem := by
        have hmem := zag_cycleMinPos_mem_cycleMinima next.out.order
          next.out.vertical next.out.point
        rwa [next.root_eq] at hmem
      first_lt_middle := first_lt_middle
      middle_lt_third := middle_lt_third
    }
    (zagFullMerge ⟨e, π, first, .prepend first middle third first_mem middle_mem
      first_lt_middle middle_lt_third tail⟩).out =
      ⟨zagResidualMergeOrder next.out.order next.out.vertical m next.out.point
          next.out.point_property next.root_eq,
        zagResidualMergeVertical next.out.order next.out.vertical m next.out.point,
        next.out.point,
        zagResidualMergePoint_nontrivialAntiExceedance next.out.order
          next.out.vertical m next.out.point next.out.point_property next.root_eq⟩ := by
  dsimp only [zagFullMerge]
  rw [zagFullMergeCore.eq_1]

theorem zagFullMerge_fullSlice {n : ℕ} (p : ZagPointedPlane n) :
    (zagFullMerge (zagFullSlice p).out).out = p := by
  classical
  fun_induction zagFullSlice p with
  | case1 p e' π' hres m p' next hmfirst hmmiddle hmiddle_root ih2 ih1 =>
      rw [zagFullMerge_prepend_out]
      let innerResult := zagFullMerge ⟨next.out.order, next.out.vertical,
        next.out.root, next.out.marks⟩
      let inner := innerResult.out
      let m₂ : ZagMarkedTriple inner.order inner.vertical := {
        first := m.first
        middle := m.middle
        third := next.out.root
        first_mem := innerResult.preserves_before m.first
          (m.first_lt_middle.trans hmiddle_root) hmfirst
        middle_mem := innerResult.preserves_before m.middle hmiddle_root hmmiddle
        third_mem := by
          have hmem := zag_cycleMinPos_mem_cycleMinima inner.order inner.vertical
            inner.point
          rwa [innerResult.root_eq] at hmem
        first_lt_middle := m.first_lt_middle
        middle_lt_third := hmiddle_root
      }
      let r₂ : ZagResidualMarkedPlane n :=
        ⟨inner.order, inner.vertical, m₂, inner.point, inner.point_property,
          innerResult.root_eq⟩
      let r₁ : ZagResidualMarkedPlane n :=
        ⟨p'.order, p'.vertical, m, p'.point, p'.point_property,
          zagSliceResidualTriple_third p.order p.vertical p.point
            p.point_property hres⟩
      have hinner : inner = p' := by
        exact ih2
      have he := congrArg ZagPointedPlane.order hinner
      have hπ := congrArg ZagPointedPlane.vertical hinner
      have hpoint := congrArg ZagPointedPlane.point hinner
      have hm : HEq m₂ m := by
        apply zagMarkedTriple_heq_of_fields he hπ
        · rfl
        · rfl
        · exact next.root_eq.trans
            (zagSliceResidualTriple_third p.order p.vertical p.point
              p.point_property hres).symm
      have hr : r₂ = r₁ := by
        exact zagResidualMarkedPlane_ext he hπ hm hpoint
      change zagMergeStep (Sum.inr r₂) = p
      rw [hr]
      apply zagPointedPlane_ext
      · exact
          zagResidualMerge_slice_order p.order p.vertical p.point
            p.point_property hres
      · exact
          zagResidualMerge_slice_vertical p.order p.vertical p.point
            p.point_property hres
      · rfl
  | case2 p e' π' hterm m =>
      rw [zagFullMerge_terminal_out]
      apply zagPointedPlane_ext
      · exact zagMerge_slice_terminal_order p.order p.vertical p.point
          p.point_property hterm
      · exact zagMerge_slice_terminal_vertical p.order p.vertical p.point
          p.point_property hterm
      · exact zagMerge_slice_terminal_point p.order p.vertical p.point
          p.point_property hterm

theorem zagFullSlice_fullMerge {n : ℕ} (q : ZagOddMarkedPlane n) :
    (zagFullSlice (zagFullMerge q).out).out = q := by
  classical
  rcases q with ⟨e, π, root, marks⟩
  induction marks with
  | terminal m =>
      let marked : ZagMarkedPlane n := ⟨e, π, m⟩
      have hs : zagSliceStep (zagMergeStep (Sum.inl marked)) =
          Sum.inl marked := zagSliceStep_mergeStep_terminal marked
      have hf := zagFullSlice_of_terminal
        (zagMergeStep (Sum.inl marked)) marked hs
      rw [zagFullMerge_terminal_out]
      change (zagFullSlice (zagMergeStep (Sum.inl marked))).out = _
      simpa only [marked] using hf
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      let next := zagFullMerge ⟨e, π, third, tail⟩
      let m : ZagMarkedTriple next.out.order next.out.vertical := {
        first := first
        middle := middle
        third := third
        first_mem := next.preserves_before first
          (first_lt_middle.trans middle_lt_third) first_mem
        middle_mem := next.preserves_before middle middle_lt_third middle_mem
        third_mem := by
          have hmem := zag_cycleMinPos_mem_cycleMinima next.out.order
            next.out.vertical next.out.point
          rwa [next.root_eq] at hmem
        first_lt_middle := first_lt_middle
        middle_lt_third := middle_lt_third
      }
      let residual : ZagResidualMarkedPlane n :=
        ⟨next.out.order, next.out.vertical, m, next.out.point,
          next.out.point_property, next.root_eq⟩
      have hs : zagSliceStep (zagMergeStep (Sum.inr residual)) =
          Sum.inr residual := zagSliceStep_mergeStep_residual residual
      have hf := zagFullSlice_of_residual
        (zagMergeStep (Sum.inr residual)) residual hs
      rw [zagFullMerge_prepend_out]
      change (zagFullSlice (zagMergeStep (Sum.inr residual))).out = _
      rw [hf]
      have horder : (zagFullSlice next.out).out.order = e :=
        congrArg (fun q : ZagOddMarkedPlane n => q.order) ih
      have hvertical : (zagFullSlice next.out).out.vertical = π :=
        congrArg (fun q : ZagOddMarkedPlane n => q.vertical) ih
      have htail : (zagFullSlice next.out).out.marks.toList = tail.toList :=
        congrArg (fun q : ZagOddMarkedPlane n => q.marks.toList) ih
      apply zagOddMarkedPlane_ext_toList
      · change (zagFullSlice next.out).out.order = e
        exact horder
      · change (zagFullSlice next.out).out.vertical = π
        exact hvertical
      · rfl
      · simp only [ZagOddMarks.toList]
        change first :: middle :: (zagFullSlice next.out).out.marks.toList =
          first :: middle :: tail.toList
        exact congrArg (fun xs => first :: middle :: xs) htail

end MetaMathlibExt
