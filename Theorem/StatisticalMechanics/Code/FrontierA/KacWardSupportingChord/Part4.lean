/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardExtremeVertex
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Def.StatisticalMechanics.Code.FrontierA.KacWardSupportingChord.Part3


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_strictlySeparated
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsep : polygon.VertexOneStrictlySeparated) :
    polygon.VertexOneDiagonalIsClean := by
  let A := polygon.vertex 0
  let C := polygon.vertex 2
  let side := fun k : Fin (m + 3) ↦
    kwComplexCross (C - A) (polygon.vertex k - A)
  have hrest_ne (k : Fin (m + 3)) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
      (hk2 : k ≠ 2) : side k ≠ 0 := by
    rcases hsep with hneg | hpos
    · exact ne_of_lt (hneg.2 k hk0 hk1 hk2)
    · exact ne_of_gt (hpos.2 k hk0 hk1 hk2)
  constructor
  · intro k hk0 hk1 hk2 hbetween
    exact hrest_ne k hk0 hk1 hk2
      (kwComplexCross_eq_zero_of_sbtw hbetween)
  · intro k hk0 hk1
    by_cases hk2 : k = 2
    · subst k
      rw [Set.disjoint_left]
      intro z hzAC hzCD
      have h30 : (2 : Fin (m + 3)) + 1 ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hval
      have h31 : (2 : Fin (m + 3)) + 1 ≠ 1 := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hval
      have h32 : (2 : Fin (m + 3)) + 1 ≠ 2 :=
        polygon.add_one_ne_self 2
      have hcross : kwComplexCross (A - C)
          (polygon.vertex (2 + 1) - C) ≠ 0 := by
        have h := hrest_ne (2 + 1) h30 h31 h32
        unfold side at h
        unfold A C at h ⊢
        convert neg_ne_zero.mpr h using 1 <;>
          unfold kwComplexCross <;>
          simp only [Complex.sub_re, Complex.sub_im] <;>
          ring
      exact Set.disjoint_left.mp
        (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
        ((sbtw_comm).mpr hzAC) hzCD
    · by_cases hsucc0 : k + 1 = 0
      · rw [Set.disjoint_left]
        intro z hzAC hzKA
        have hcross : kwComplexCross (C - A)
            (polygon.vertex k - A) ≠ 0 := hrest_ne k hk0 hk1 hk2
        exact Set.disjoint_left.mp
          (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
          hzAC ((sbtw_comm).mpr (by simpa only [hsucc0] using hzKA))
      · have hsucc1 : k + 1 ≠ 1 := by
          intro h
          apply hk0
          apply add_right_cancel (b := (1 : Fin (m + 3)))
          simpa only [zero_add] using h
        have hsucc2 : k + 1 ≠ 2 := by
          intro h
          apply hk1
          have hone : (1 : Fin (m + 3)) + 1 = 2 := by
            apply Fin.ext
            simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
          exact add_right_cancel (h.trans hone.symm)
        rcases hsep with hneg | hpos
        · exact kw_openSegments_disjoint_of_cross_same_sign
            (Or.inr ⟨hneg.2 k hk0 hk1 hk2,
              hneg.2 (k + 1) hsucc0 hsucc1 hsucc2⟩)
        · exact kw_openSegments_disjoint_of_cross_same_sign
            (Or.inl ⟨hpos.2 k hk0 hk1 hk2,
              hpos.2 (k + 1) hsucc0 hsucc1 hsucc2⟩)


theorem KWFiniteSimplePolygon.vertexOneAlignedSideEar_of_strictlySeparated
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsep : polygon.VertexOneStrictlySeparated) :
    polygon.VertexOneAlignedSideEar := by
  let side := fun k : Fin (m + 3) ↦
    kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
      (polygon.vertex k - polygon.vertex 0)
  have hzeroOne : (0 : Fin (m + 3)) + 1 = 1 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
  have honeTwo : (1 : Fin (m + 3)) + 1 = 2 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have htwoThree : (2 : Fin (m + 3)) + 1 = 3 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  let previousIndex : Fin (m + 3) := ⟨m + 2, by omega⟩
  have hpreviousIndex : previousIndex = (-1 : Fin (m + 3)) := by
    apply Fin.ext
    simp [previousIndex, Fin.val_neg]
  have hpreviousNext : previousIndex + 1 = 0 := by
    rw [hpreviousIndex]
    abel
  have hp0 : previousIndex ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [previousIndex] at this
  have hp1 : previousIndex ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp [previousIndex] at this
  have hp2 : previousIndex ≠ 2 := by
    intro h
    have := congrArg Fin.val h
    simp [previousIndex, Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at this
    omega
  have h30 : (3 : Fin (m + 3)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at this
  have h31 : (3 : Fin (m + 3)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at this
  have h32 : (3 : Fin (m + 3)) ≠ 2 := by
    intro h
    exact polygon.add_one_ne_self 2 (htwoThree.trans h)
  have hmiddle : kwComplexCross (polygon.edgeVector 0)
      (polygon.edgeVector 1) = -side 1 := by
    unfold KWFiniteSimplePolygon.edgeVector side
    rw [hzeroOne, honeTwo]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hdiagonal : polygon.edgeVector 0 + polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [hzeroOne, honeTwo]
    ring
  have hleft : kwComplexCross (polygon.edgeVector (-1))
      (polygon.edgeVector 0 + polygon.edgeVector 1) = side previousIndex := by
    rw [← hpreviousIndex, hdiagonal]
    unfold KWFiniteSimplePolygon.edgeVector side
    rw [hpreviousNext]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hright : kwComplexCross
      (polygon.edgeVector 0 + polygon.edgeVector 1)
      (polygon.edgeVector 2) = side 3 := by
    rw [hdiagonal]
    unfold KWFiniteSimplePolygon.edgeVector side
    rw [htwoThree]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  refine ⟨polygon.vertexOneDiagonalIsClean_of_strictlySeparated hm hsep,
    ?_, ?_, ?_⟩
  · rw [hmiddle]
    rcases hsep with hpos | hneg
    · exact neg_ne_zero.mpr (ne_of_gt hpos.1)
    · exact neg_ne_zero.mpr (ne_of_lt hneg.1)
  · rw [hmiddle, hleft]
    rcases hsep with hpos | hneg
    · exact Or.inr ⟨neg_neg_of_pos hpos.1,
        hpos.2 previousIndex hp0 hp1 hp2⟩
    · exact Or.inl ⟨neg_pos_of_neg hneg.1,
        hneg.2 previousIndex hp0 hp1 hp2⟩
  · rw [hmiddle, hright]
    rcases hsep with hpos | hneg
    · exact Or.inr ⟨neg_neg_of_pos hpos.1, hpos.2 3 h30 h31 h32⟩
    · exact Or.inl ⟨neg_pos_of_neg hneg.1, hneg.2 3 h30 h31 h32⟩

end StatMech.FrontierA
