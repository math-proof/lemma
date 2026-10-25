/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part5


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.vertexOneRemovalIsSimple_of_diagonalIsClean
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3))
    (hclean : polygon.VertexOneDiagonalIsClean) :
    polygon.VertexOneRemovalIsSimple := by
  let f : Fin (m + 2) → Fin (m + 3) :=
    (1 : Fin (m + 3)).succAbove
  have hfInjective : Function.Injective f :=
    Fin.succAbove_right_injective
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 2 := by simp [f]
  constructor
  · intro i j hji hjsucc
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (hji rfl).elim
        | succ s =>
            have hk0 : f s.succ ≠ 0 := by
              rw [← hf0]
              exact hfInjective.ne (by simp)
            have hk1 : f s.succ ≠ 1 :=
              Fin.succAbove_ne (1 : Fin (m + 3)) s.succ
            have hk2 : f s.succ ≠ 2 := by
              rw [← hf1]
              exact hfInjective.ne hjsucc
            simpa only [kwRemoveVertexOne, f] using
              hclean.1 (f s.succ) hk0 hk1 hk2
    | succ q =>
        let old : Fin (m + 3) := f q.succ
        have hendVertex : polygon.vertex (f (q.succ + 1)) =
            polygon.vertex (old + 1) := by
          simpa only [f, old, kwRemoveVertexOne] using
            kwRemoveVertexOne_succ_add_one polygon.vertex q
        have hend : f (q.succ + 1) = old + 1 :=
          polygon.vertex_injective hendVertex
        have hjOld : f j ≠ old := hfInjective.ne hji
        have hjEnd : f j ≠ old + 1 := by
          rw [← hend]
          exact hfInjective.ne hjsucc
        change ¬Sbtw ℝ (polygon.vertex (f q.succ))
          (polygon.vertex (f j)) (polygon.vertex (f (q.succ + 1)))
        rw [hend]
        exact polygon.vertex_not_strictly_between old (f j) hjOld hjEnd
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ qj =>
            have hk0 : f qj.succ ≠ 0 := by
              rw [← hf0]
              exact hfInjective.ne (by simp)
            have hk1 : f qj.succ ≠ 1 :=
              Fin.succAbove_ne (1 : Fin (m + 3)) qj.succ
            change Disjoint
              {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)}
              {z : ℂ | Sbtw ℝ (polygon.vertex (f qj.succ)) z
                (polygon.vertex (f (qj.succ + 1)))}
            have hendVertex : polygon.vertex (f (qj.succ + 1)) =
                polygon.vertex (f qj.succ + 1) := by
              simpa only [f, kwRemoveVertexOne] using
                kwRemoveVertexOne_succ_add_one polygon.vertex qj
            rw [hendVertex]
            exact hclean.2 (f qj.succ) hk0 hk1
    | succ qi =>
        cases j using Fin.cases with
        | zero =>
            have hk0 : f qi.succ ≠ 0 := by
              rw [← hf0]
              exact hfInjective.ne (by simp)
            have hk1 : f qi.succ ≠ 1 :=
              Fin.succAbove_ne (1 : Fin (m + 3)) qi.succ
            have hendVertex : polygon.vertex (f (qi.succ + 1)) =
                polygon.vertex (f qi.succ + 1) := by
              simpa only [f, kwRemoveVertexOne] using
                kwRemoveVertexOne_succ_add_one polygon.vertex qi
            change Disjoint
              {z : ℂ | Sbtw ℝ (polygon.vertex (f qi.succ)) z
                (polygon.vertex (f (qi.succ + 1)))}
              {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)}
            rw [hendVertex]
            exact (hclean.2 (f qi.succ) hk0 hk1).symm
        | succ qj =>
            have holdNe : f qi.succ ≠ f qj.succ := hfInjective.ne hij
            have hiEndVertex : polygon.vertex (f (qi.succ + 1)) =
                polygon.vertex (f qi.succ + 1) := by
              simpa only [f, kwRemoveVertexOne] using
                kwRemoveVertexOne_succ_add_one polygon.vertex qi
            have hjEndVertex : polygon.vertex (f (qj.succ + 1)) =
                polygon.vertex (f qj.succ + 1) := by
              simpa only [f, kwRemoveVertexOne] using
                kwRemoveVertexOne_succ_add_one polygon.vertex qj
            change Disjoint
              {z : ℂ | Sbtw ℝ (polygon.vertex (f qi.succ)) z
                (polygon.vertex (f (qi.succ + 1)))}
              {z : ℂ | Sbtw ℝ (polygon.vertex (f qj.succ)) z
                (polygon.vertex (f (qj.succ + 1)))}
            rw [hiEndVertex, hjEndVertex]
            exact polygon.edgeInteriors_disjoint (f qi.succ) (f qj.succ)
              holdNe


theorem KWFiniteSimplePolygon.outerTurns_ne_pi_of_diagonalIsClean
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hclean : polygon.VertexOneDiagonalIsClean) :
    (Complex.arg (polygon.edgeVector 0 + polygon.edgeVector 1) :
          Real.Angle) -
        (Complex.arg (polygon.edgeVector (-1)) : Real.Angle) ≠
          (Real.pi : Real.Angle) ∧
      (Complex.arg (polygon.edgeVector 2) : Real.Angle) -
        (Complex.arg (polygon.edgeVector 0 + polygon.edgeVector 1) :
          Real.Angle) ≠ (Real.pi : Real.Angle) := by
  have hn : 4 ≤ m + 3 := by omega
  have hprevSucc : (-1 : Fin (m + 3)) + 1 = 0 := by abel
  have h01 : (0 : Fin (m + 3)) + 1 = 1 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
  have h12 : (1 : Fin (m + 3)) + 1 = 2 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have h23 : (2 : Fin (m + 3)) + 1 = 3 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have hprev0 : (-1 : Fin (m + 3)) ≠ 0 := by
    intro h
    have heq := congrArg (fun k : Fin (m + 3) ↦ k + 1) h
    have h10 : (1 : Fin (m + 3)) ≠ 0 := by
      simpa only [h01] using polygon.add_one_ne_self 0
    exact h10 (by simpa only [hprevSucc, zero_add] using heq.symm)
  have h30 : (3 : Fin (m + 3)) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hval
  have h31 : (3 : Fin (m + 3)) ≠ 1 := by
    intro h
    have hval := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 1 < m + 3)] at hval
  have h32 : (3 : Fin (m + 3)) ≠ 2 := by
    intro h
    have hval := congrArg Fin.val h
    norm_num [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hval
  have h02 : (0 : Fin (m + 3)) ≠ 2 := by
    exact (polygon.add_two_ne_self 0).symm
  have h03 : (0 : Fin (m + 3)) ≠ 3 := h30.symm
  have h20 : (2 : Fin (m + 3)) ≠ 0 := h02.symm
  have hprev1 : (-1 : Fin (m + 3)) ≠ 1 := by
    intro h
    have heq := congrArg (fun k : Fin (m + 3) ↦ k + 1) h
    exact h20 (by simpa only [hprevSucc, h12] using heq.symm)
  have hprev2 : (-1 : Fin (m + 3)) ≠ 2 := by
    intro h
    have heq := congrArg (fun k : Fin (m + 3) ↦ k + 1) h
    exact h30 (by simpa only [hprevSucc, h23] using heq.symm)
  have h2prev : (2 : Fin (m + 3)) ≠ -1 := hprev2.symm
  have h2prevSucc : (2 : Fin (m + 3)) ≠ (-1) + 1 := by
    simpa only [hprevSucc] using h20
  have h0three : (0 : Fin (m + 3)) ≠ 2 + 1 := by
    simpa only [h23] using h03
  have hleft := kw_angle_diagonal_ne_pi_of_no_between
    (polygon.vertex_injective.ne hprev0)
    (polygon.vertex_injective.ne h02)
    (polygon.vertex_injective.ne hprev2)
    (hclean.1 (-1) hprev0 hprev1 hprev2)
    (by
      simpa only [hprevSucc] using
        polygon.vertex_not_strictly_between (-1) 2 h2prev h2prevSucc)
  have hright := kw_angle_diagonal_ne_pi_of_no_between
    (polygon.vertex_injective.ne h02)
    (polygon.vertex_injective.ne h32.symm)
    (polygon.vertex_injective.ne h03)
    (by
      simpa only [h23] using
        polygon.vertex_not_strictly_between 2 0 h02 h0three)
    (hclean.1 3 h30 h31 h32)
  have heprev : polygon.edgeVector (-1) =
      polygon.vertex 0 - polygon.vertex (-1) := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [hprevSucc]
  have he0 : polygon.edgeVector 0 =
      polygon.vertex 1 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [h01]
  have he1 : polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 1 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [h12]
  have he2 : polygon.edgeVector 2 =
      polygon.vertex 3 - polygon.vertex 2 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [h23]
  have hdiag : polygon.edgeVector 0 + polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 0 := by
    rw [he0, he1]
    ring
  rw [heprev, he2, hdiag]
  exact ⟨hleft, hright⟩


theorem KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_between
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3))
    (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1)
      (polygon.vertex 2)) :
    polygon.VertexOneDiagonalIsClean := by
  constructor
  · exact polygon.not_sbtw_zero_two_of_between hbetween
  · exact polygon.diagonal_zero_two_disjoint hbetween


theorem KWFiniteSimplePolygon.vertexOneRemovalIsSimple_of_between
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3))
    (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1)
      (polygon.vertex 2)) :
    polygon.VertexOneRemovalIsSimple := by
  exact polygon.vertexOneRemovalIsSimple_of_diagonalIsClean
    (polygon.vertexOneDiagonalIsClean_of_between hbetween)


end StatMech.FrontierA
