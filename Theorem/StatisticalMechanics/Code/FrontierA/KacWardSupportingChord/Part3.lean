/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardExtremeVertex
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Def.StatisticalMechanics.Code.FrontierA.KacWardSupportingChord.Part2


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_strictlyOneSided
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hside : polygon.VertexZeroTwoStrictlyOneSided) :
    polygon.VertexOneDiagonalIsClean := by
  let A := polygon.vertex 0
  let C := polygon.vertex 2
  have h02 : (0 : Fin (m + 3)) ≠ 2 := by
    simpa only [zero_add] using (polygon.add_two_ne_self 0).symm
  have hcross_ne (k : Fin (m + 3)) (hk0 : k ≠ 0) (hk2 : k ≠ 2) :
      kwComplexCross (C - A) (polygon.vertex k - A) ≠ 0 := by
    rcases hside with hpos | hneg
    · exact ne_of_gt (hpos k hk0 hk2)
    · exact ne_of_lt (hneg k hk0 hk2)
  constructor
  · intro k hk0 _hk1 hk2 hbetween
    exact hcross_ne k hk0 hk2
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
      have h32 : (2 : Fin (m + 3)) + 1 ≠ 2 :=
        polygon.add_one_ne_self 2
      have hcross : kwComplexCross (A - C)
          (polygon.vertex (2 + 1) - C) ≠ 0 := by
        have h := hcross_ne (2 + 1) h30 h32
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
            (polygon.vertex k - A) ≠ 0 := hcross_ne k hk0 hk2
        exact Set.disjoint_left.mp
          (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
          hzAC ((sbtw_comm).mpr (by simpa only [hsucc0] using hzKA))
      · have hsucc2 : k + 1 ≠ 2 := by
          intro h
          apply hk1
          have hone : (1 : Fin (m + 3)) + 1 = 2 := by
            apply Fin.ext
            simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
          exact add_right_cancel (h.trans hone.symm)
        rcases hside with hpos | hneg
        · exact kw_openSegments_disjoint_of_cross_same_sign
            (Or.inl ⟨hpos k hk0 hk2,
              hpos (k + 1) hsucc0 hsucc2⟩)
        · exact kw_openSegments_disjoint_of_cross_same_sign
            (Or.inr ⟨hneg k hk0 hk2,
              hneg (k + 1) hsucc0 hsucc2⟩)


end StatMech.FrontierA
