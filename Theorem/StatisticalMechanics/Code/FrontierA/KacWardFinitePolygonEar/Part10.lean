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
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part9


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.rotated_vertexOneCrossEar_of_sign
    (polygon : KWFiniteSimplePolygon 4)
    (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (i : Fin 4)
    (hsign :
      (0 < kwComplexCross (polygon.edgeVector (i + 3))
            (polygon.edgeVector i) ∧
        0 < kwComplexCross (polygon.edgeVector i)
            (polygon.edgeVector (i + 1)) ∧
        0 < kwComplexCross (polygon.edgeVector (i + 2))
            (polygon.edgeVector (i + 3))) ∨
      (kwComplexCross (polygon.edgeVector (i + 3))
              (polygon.edgeVector i) < 0 ∧
        kwComplexCross (polygon.edgeVector i)
              (polygon.edgeVector (i + 1)) < 0 ∧
        kwComplexCross (polygon.edgeVector (i + 2))
              (polygon.edgeVector (i + 3)) < 0)) :
    (polygon.rotate i).VertexOneCrossEar := by
  have hsum : polygon.edgeVector (i + 3) + polygon.edgeVector i +
      polygon.edgeVector (i + 1) + polygon.edgeVector (i + 2) = 0 := by
    have h := polygon.quadrilateral_edge_sum i
    linear_combination h
  have hbqRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear (i + 1)
  have hi : i + 1 + 1 = i + 2 := by
    rw [add_assoc]
    have h : (1 : Fin 4) + 1 = 2 := by decide
    rw [h]
  have hbq : kwComplexCross (polygon.edgeVector (i + 1))
      (polygon.edgeVector (i + 2)) ≠ 0 := by
    simpa only [hi] using hbqRaw
  have hcert := kw_fourVector_crossEar
    (polygon.edgeVector (i + 3)) (polygon.edgeVector i)
    (polygon.edgeVector (i + 1)) (polygon.edgeVector (i + 2))
    (polygon.edgeVector_ne_zero (i + 1))
    (polygon.edgeVector_ne_zero (i + 2)) hsum hbq hsign
  have hprev : (-1 : Fin 4) + i = i + 3 := by
    have hm : (-1 : Fin 4) = 3 := by decide
    rw [hm, add_comm]
  have h0 : (0 : Fin 4) + i = i := by simp
  have h1 : (1 : Fin 4) + i = i + 1 := by abel
  have h2 : (2 : Fin 4) + i = i + 2 := by abel
  simpa only [KWFiniteSimplePolygon.VertexOneCrossEar,
    KWFiniteSimplePolygon.rotate_edgeVector, hprev, h0, h1, h2] using hcert


theorem KWFiniteSimplePolygon.exists_rotated_vertexOneCrossEar_four
    (polygon : KWFiniteSimplePolygon 4)
    (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    ∃ r : Fin 4, (polygon.rotate r).VertexOneCrossEar := by
  let s0 := kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1)
  let s1 := kwComplexCross (polygon.edgeVector 1) (polygon.edgeVector 2)
  let s2 := kwComplexCross (polygon.edgeVector 2) (polygon.edgeVector 3)
  let s3 := kwComplexCross (polygon.edgeVector 3) (polygon.edgeVector 0)
  have h0 : s0 ≠ 0 :=
    polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear 0
  have h1 : s1 ≠ 0 :=
    polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear 1
  have h2 : s2 ≠ 0 :=
    polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear 2
  have h3 : s3 ≠ 0 :=
    polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear 3
  have hNo02 : ¬(s0 * s3 < 0 ∧ s1 * s2 < 0) :=
    polygon.quadrilateral_not_cross_pattern_zero_two
  have hNo13 : ¬(s1 * s0 < 0 ∧ s2 * s3 < 0) :=
    polygon.quadrilateral_not_cross_pattern_one_three
  rcases kw_four_signs_have_ear h0 h1 h2 h3 hNo02 hNo13 with
      h | h | h | h
  · refine ⟨0, polygon.rotated_vertexOneCrossEar_of_sign
      hnoncollinear 0 ?_⟩
    simpa [s0, s2, s3, Fin.add_def] using h
  · refine ⟨1, polygon.rotated_vertexOneCrossEar_of_sign
      hnoncollinear 1 ?_⟩
    simpa [s0, s1, s3, Fin.add_def] using h
  · refine ⟨2, polygon.rotated_vertexOneCrossEar_of_sign
      hnoncollinear 2 ?_⟩
    simpa [s0, s1, s2, Fin.add_def] using h
  · refine ⟨3, polygon.rotated_vertexOneCrossEar_of_sign
      hnoncollinear 3 ?_⟩
    simpa [s1, s2, s3, Fin.add_def] using h


theorem KWFiniteSimplePolygon.vertexOneDiagonalIsClean_four_of_crossEar
    (polygon : KWFiniteSimplePolygon 4)
    (hear : polygon.VertexOneCrossEar) :
    polygon.VertexOneDiagonalIsClean := by
  have he0 : polygon.edgeVector 0 =
      polygon.vertex 1 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he1 : polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 1 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he2 : polygon.edgeVector 2 =
      polygon.vertex 3 - polygon.vertex 2 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have he3 : polygon.edgeVector 3 =
      polygon.vertex 0 - polygon.vertex 3 := by
    unfold KWFiniteSimplePolygon.edgeVector
    congr 2
  have hdiag : polygon.edgeVector 0 + polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 0 := by
    rw [he0, he1]
    ring
  have hminus : (-1 : Fin 4) = 3 := by decide
  have hleft : kwComplexCross (polygon.edgeVector 3)
      (polygon.edgeVector 0 + polygon.edgeVector 1) ≠ 0 := by
    rw [← hminus]
    rcases hear.2.2.1 with h | h <;> nlinarith [h.2]
  have hright : kwComplexCross
      (polygon.edgeVector 0 + polygon.edgeVector 1)
      (polygon.edgeVector 2) ≠ 0 := by
    rcases hear.2.2.2 with h | h <;> nlinarith [h.2]
  have hv30 : polygon.vertex 3 - polygon.vertex 0 =
      -polygon.edgeVector 3 := by
    rw [he3]
    ring
  have hvertex3 : kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
      (polygon.vertex 3 - polygon.vertex 0) ≠ 0 := by
    rw [← hdiag, hv30, kwComplexCross_neg_right,
      kwComplexCross_swap]
    simpa using hleft
  constructor
  · intro k hk0 hk1 hk2
    fin_cases k
    · exact (hk0 rfl).elim
    · exact (hk1 rfl).elim
    · exact (hk2 rfl).elim
    · intro hbetween
      exact hvertex3 (kwComplexCross_eq_zero_of_sbtw hbetween)
  · intro k hk0 hk1
    fin_cases k
    · exact (hk0 rfl).elim
    · exact (hk1 rfl).elim
    · have hcross : kwComplexCross
          (polygon.vertex 0 - polygon.vertex 2)
          (polygon.vertex 3 - polygon.vertex 2) ≠ 0 := by
        intro hz
        apply hright
        have hv02 : polygon.vertex 0 - polygon.vertex 2 =
            -(polygon.vertex 2 - polygon.vertex 0) := by ring
        rw [hv02, ← hdiag, ← he2] at hz
        unfold kwComplexCross at hz ⊢
        simp only [Complex.neg_re, Complex.neg_im] at hz
        linear_combination -hz
      have hcommon :=
        kw_openSegments_disjoint_of_common_left_cross_ne hcross
      rw [Set.disjoint_left]
      intro z hzdiag hzedge
      exact Set.disjoint_left.mp hcommon
        ((sbtw_comm).mpr hzdiag) hzedge
    · have hcommon :=
        kw_openSegments_disjoint_of_common_left_cross_ne hvertex3
      rw [Set.disjoint_left]
      intro z hzdiag hzedge
      exact Set.disjoint_left.mp hcommon hzdiag
        ((sbtw_comm).mpr hzedge)


theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_crossEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneCrossEar) :
    polygon.VertexOnePhaseEar hm := by
  have hlocal := kwVectorTurnPhase_ear_splice
    (polygon.edgeVector (-1)) (polygon.edgeVector 0)
    (polygon.edgeVector 1) (polygon.edgeVector 2)
    (polygon.edgeVector_ne_zero (-1))
    (polygon.edgeVector_ne_zero 0)
    (polygon.edgeVector_ne_zero 1)
    (polygon.edgeVector_ne_zero 2)
    hear.1 hear.2.1 hear.2.2.1 hear.2.2.2
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal


theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_alignedSideEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (hear : polygon.VertexOneAlignedSideEar) :
    polygon.VertexOnePhaseEar hm := by
  have hpreviousRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear (-1)
  have hpreviousIndex : (-1 : Fin (m + 3)) + 1 = 0 := by abel
  have hprevious : kwComplexCross (polygon.edgeVector (-1))
      (polygon.edgeVector 0) ≠ 0 := by
    simpa only [hpreviousIndex] using hpreviousRaw
  have hnextRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear 1
  have hnextIndex : (1 : Fin (m + 3)) + 1 = 2 := by abel
  have hnext : kwComplexCross (polygon.edgeVector 1)
      (polygon.edgeVector 2) ≠ 0 := by
    simpa only [hnextIndex] using hnextRaw
  have hlocal := kwAngleTurnPhase_ear_splice_of_interiorSides
    (polygon.edgeVector (-1)) (polygon.edgeVector 0)
    (polygon.edgeVector 1) (polygon.edgeVector 2)
    (polygon.edgeVector_ne_zero (-1))
    (polygon.edgeVector_ne_zero 0)
    (polygon.edgeVector_ne_zero 1)
    (polygon.edgeVector_ne_zero 2)
    hprevious hear.2.1 hnext hear.2.2.1 hear.2.2.2
  change kwVectorTurnPhase (polygon.edgeVector (-1))
        (polygon.edgeVector 0) *
      kwVectorTurnPhase (polygon.edgeVector 0)
        (polygon.edgeVector 1) *
      kwVectorTurnPhase (polygon.edgeVector 1)
        (polygon.edgeVector 2) =
    kwVectorTurnPhase (polygon.edgeVector (-1))
        (polygon.edgeVector 0 + polygon.edgeVector 1) *
      kwVectorTurnPhase
        (polygon.edgeVector 0 + polygon.edgeVector 1)
        (polygon.edgeVector 2) at hlocal
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal


theorem KWFiniteSimplePolygon.vertexOneGeometricEar_of_alignedSideEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (hear : polygon.VertexOneAlignedSideEar) :
    polygon.VertexOneGeometricEar hm := by
  exact ⟨hear.1,
    polygon.vertexOnePhaseEar_of_alignedSideEar hm hnoncollinear hear⟩


theorem kwVectorTurnPhase_ear_splice_of_doubleNoWrap
    (previous incoming outgoing next : ℂ)
    (hi : incoming ≠ 0) (ho : outgoing ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hleft : kwAngleTurnNoWrap
      (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg (incoming + outgoing) : Real.Angle))
    (hright : kwAngleTurnNoWrap
      (Complex.arg (incoming + outgoing) : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  have hleftPhase := kwAngleTurnPhase_mul_of_sign_or_outer
    (Complex.arg previous : Real.Angle)
    (Complex.arg incoming : Real.Angle)
    (Complex.arg (incoming + outgoing) : Real.Angle)
    hleft.1 hleft.2.1 hleft.2.2
  have hrightPhase := kwAngleTurnPhase_mul_of_sign_or_outer
    (Complex.arg (incoming + outgoing) : Real.Angle)
    (Complex.arg outgoing : Real.Angle)
    (Complex.arg next : Real.Angle)
    hright.1 hright.2.1 hright.2.2
  have hmiddlePhase := kwAngleTurnPhase_vector_sum hi ho hmiddle
  change kwVectorTurnPhase previous incoming *
      kwVectorTurnPhase incoming (incoming + outgoing) =
        kwVectorTurnPhase previous (incoming + outgoing) at hleftPhase
  change kwVectorTurnPhase (incoming + outgoing) outgoing *
      kwVectorTurnPhase outgoing next =
        kwVectorTurnPhase (incoming + outgoing) next at hrightPhase
  change kwVectorTurnPhase incoming (incoming + outgoing) *
      kwVectorTurnPhase (incoming + outgoing) outgoing =
        kwVectorTurnPhase incoming outgoing at hmiddlePhase
  rw [← hmiddlePhase]
  calc
    kwVectorTurnPhase previous incoming *
          (kwVectorTurnPhase incoming (incoming + outgoing) *
            kwVectorTurnPhase (incoming + outgoing) outgoing) *
          kwVectorTurnPhase outgoing next =
        (kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming (incoming + outgoing)) *
          (kwVectorTurnPhase (incoming + outgoing) outgoing *
            kwVectorTurnPhase outgoing next) := by ring
    _ = kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next := by
      rw [hleftPhase, hrightPhase]


theorem kwVectorTurnPhase_ear_splice_of_doubleWrap
    (previous incoming outgoing next : ℂ)
    (hi : incoming ≠ 0) (ho : outgoing ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hleft : kwAngleTurnWrap
      (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg (incoming + outgoing) : Real.Angle))
    (hright : kwAngleTurnWrap
      (Complex.arg (incoming + outgoing) : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  have hleftPhase := kwAngleTurnPhase_mul_eq_neg_of_wrap
    (Complex.arg previous : Real.Angle)
    (Complex.arg incoming : Real.Angle)
    (Complex.arg (incoming + outgoing) : Real.Angle)
    hleft.1 hleft.2.1 hleft.2.2.1 hleft.2.2.2.1 hleft.2.2.2.2
  have hrightPhase := kwAngleTurnPhase_mul_eq_neg_of_wrap
    (Complex.arg (incoming + outgoing) : Real.Angle)
    (Complex.arg outgoing : Real.Angle)
    (Complex.arg next : Real.Angle)
    hright.1 hright.2.1 hright.2.2.1 hright.2.2.2.1 hright.2.2.2.2
  have hmiddlePhase := kwAngleTurnPhase_vector_sum hi ho hmiddle
  change kwVectorTurnPhase previous incoming *
      kwVectorTurnPhase incoming (incoming + outgoing) =
        -kwVectorTurnPhase previous (incoming + outgoing) at hleftPhase
  change kwVectorTurnPhase (incoming + outgoing) outgoing *
      kwVectorTurnPhase outgoing next =
        -kwVectorTurnPhase (incoming + outgoing) next at hrightPhase
  change kwVectorTurnPhase incoming (incoming + outgoing) *
      kwVectorTurnPhase (incoming + outgoing) outgoing =
        kwVectorTurnPhase incoming outgoing at hmiddlePhase
  rw [← hmiddlePhase]
  calc
    kwVectorTurnPhase previous incoming *
          (kwVectorTurnPhase incoming (incoming + outgoing) *
            kwVectorTurnPhase (incoming + outgoing) outgoing) *
          kwVectorTurnPhase outgoing next =
        (kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming (incoming + outgoing)) *
          (kwVectorTurnPhase (incoming + outgoing) outgoing *
            kwVectorTurnPhase outgoing next) := by ring
    _ = (-kwVectorTurnPhase previous (incoming + outgoing)) *
          (-kwVectorTurnPhase (incoming + outgoing) next) := by
      rw [hleftPhase, hrightPhase]
    _ = kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next := by ring


theorem kwVectorTurnPhase_ear_splice_of_mixedParity
    (previous incoming outgoing next : ℂ)
    (hi : incoming ≠ 0) (ho : outgoing ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hparity :
      (kwAngleTurnNoWrap (Complex.arg previous : Real.Angle)
            (Complex.arg incoming : Real.Angle)
            (Complex.arg (incoming + outgoing) : Real.Angle) ∧
          kwAngleTurnWrap
            (Complex.arg (incoming + outgoing) : Real.Angle)
            (Complex.arg outgoing : Real.Angle)
            (Complex.arg next : Real.Angle)) ∨
        (kwAngleTurnWrap (Complex.arg previous : Real.Angle)
            (Complex.arg incoming : Real.Angle)
            (Complex.arg (incoming + outgoing) : Real.Angle) ∧
          kwAngleTurnNoWrap
            (Complex.arg (incoming + outgoing) : Real.Angle)
            (Complex.arg outgoing : Real.Angle)
            (Complex.arg next : Real.Angle))) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      -(kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next) := by
  have hmiddlePhase := kwAngleTurnPhase_vector_sum hi ho hmiddle
  change kwVectorTurnPhase incoming (incoming + outgoing) *
      kwVectorTurnPhase (incoming + outgoing) outgoing =
        kwVectorTurnPhase incoming outgoing at hmiddlePhase
  rw [← hmiddlePhase]
  rcases hparity with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hleftPhase := kwAngleTurnPhase_mul_of_sign_or_outer
      (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg (incoming + outgoing) : Real.Angle)
      hleft.1 hleft.2.1 hleft.2.2
    have hrightPhase := kwAngleTurnPhase_mul_eq_neg_of_wrap
      (Complex.arg (incoming + outgoing) : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)
      hright.1 hright.2.1 hright.2.2.1
      hright.2.2.2.1 hright.2.2.2.2
    change kwVectorTurnPhase previous incoming *
        kwVectorTurnPhase incoming (incoming + outgoing) =
          kwVectorTurnPhase previous (incoming + outgoing) at hleftPhase
    change kwVectorTurnPhase (incoming + outgoing) outgoing *
        kwVectorTurnPhase outgoing next =
          -kwVectorTurnPhase (incoming + outgoing) next at hrightPhase
    calc
      kwVectorTurnPhase previous incoming *
            (kwVectorTurnPhase incoming (incoming + outgoing) *
              kwVectorTurnPhase (incoming + outgoing) outgoing) *
            kwVectorTurnPhase outgoing next =
          (kwVectorTurnPhase previous incoming *
              kwVectorTurnPhase incoming (incoming + outgoing)) *
            (kwVectorTurnPhase (incoming + outgoing) outgoing *
              kwVectorTurnPhase outgoing next) := by ring
      _ = _ := by rw [hleftPhase, hrightPhase]; ring
  · have hleftPhase := kwAngleTurnPhase_mul_eq_neg_of_wrap
      (Complex.arg previous : Real.Angle)
      (Complex.arg incoming : Real.Angle)
      (Complex.arg (incoming + outgoing) : Real.Angle)
      hleft.1 hleft.2.1 hleft.2.2.1 hleft.2.2.2.1 hleft.2.2.2.2
    have hrightPhase := kwAngleTurnPhase_mul_of_sign_or_outer
      (Complex.arg (incoming + outgoing) : Real.Angle)
      (Complex.arg outgoing : Real.Angle)
      (Complex.arg next : Real.Angle)
      hright.1 hright.2.1 hright.2.2
    change kwVectorTurnPhase previous incoming *
        kwVectorTurnPhase incoming (incoming + outgoing) =
          -kwVectorTurnPhase previous (incoming + outgoing) at hleftPhase
    change kwVectorTurnPhase (incoming + outgoing) outgoing *
        kwVectorTurnPhase outgoing next =
          kwVectorTurnPhase (incoming + outgoing) next at hrightPhase
    calc
      kwVectorTurnPhase previous incoming *
            (kwVectorTurnPhase incoming (incoming + outgoing) *
              kwVectorTurnPhase (incoming + outgoing) outgoing) *
            kwVectorTurnPhase outgoing next =
          (kwVectorTurnPhase previous incoming *
              kwVectorTurnPhase incoming (incoming + outgoing)) *
            (kwVectorTurnPhase (incoming + outgoing) outgoing *
              kwVectorTurnPhase outgoing next) := by ring
      _ = _ := by rw [hleftPhase, hrightPhase]; ring


theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_doubleWrapEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneDoubleWrapEar) :
    polygon.VertexOnePhaseEar hm := by
  dsimp only [KWFiniteSimplePolygon.VertexOneDoubleWrapEar] at hear
  have hlocal := kwVectorTurnPhase_ear_splice_of_doubleWrap
    (polygon.edgeVector (-1)) (polygon.edgeVector 0)
    (polygon.edgeVector 1) (polygon.edgeVector 2)
    (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
    hear.2.1 hear.2.2.1 hear.2.2.2
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal


theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_strictParityEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneStrictParityEar) :
    polygon.VertexOnePhaseEar hm := by
  dsimp only [KWFiniteSimplePolygon.VertexOneStrictParityEar] at hear
  have hlocal :
      kwVectorTurnPhase (polygon.edgeVector (-1))
            (polygon.edgeVector 0) *
          kwVectorTurnPhase (polygon.edgeVector 0)
            (polygon.edgeVector 1) *
          kwVectorTurnPhase (polygon.edgeVector 1)
            (polygon.edgeVector 2) =
        kwVectorTurnPhase (polygon.edgeVector (-1))
            (polygon.edgeVector 0 + polygon.edgeVector 1) *
          kwVectorTurnPhase
            (polygon.edgeVector 0 + polygon.edgeVector 1)
            (polygon.edgeVector 2) := by
    rcases hear.2.2 with hnowrap | hwrap
    · exact kwVectorTurnPhase_ear_splice_of_doubleNoWrap
        (polygon.edgeVector (-1)) (polygon.edgeVector 0)
        (polygon.edgeVector 1) (polygon.edgeVector 2)
        (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
        hear.2.1 hnowrap.1 hnowrap.2
    · exact kwVectorTurnPhase_ear_splice_of_doubleWrap
        (polygon.edgeVector (-1)) (polygon.edgeVector 0)
        (polygon.edgeVector 1) (polygon.edgeVector 2)
        (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
        hear.2.1 hwrap.1 hwrap.2
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal


theorem KWFiniteSimplePolygon.vertexOneGeometricEar_of_strictParityEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneStrictParityEar) :
    polygon.VertexOneGeometricEar hm := by
  exact ⟨hear.1, polygon.vertexOnePhaseEar_of_strictParityEar hm hear⟩


theorem KWFiniteSimplePolygon.vertexOneStrictParityEar_of_geometricEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (hear : polygon.VertexOneGeometricEar hm) :
    polygon.VertexOneStrictParityEar := by
  have hmiddle := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear 0
  have h01 : (0 : Fin (m + 3)) + 1 = 1 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
  rw [h01] at hmiddle
  have hpreviousRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear (-1)
  have hpreviousIndex : (-1 : Fin (m + 3)) + 1 = 0 := by abel
  have hprevious : kwComplexCross (polygon.edgeVector (-1))
      (polygon.edgeVector 0) ≠ 0 := by
    simpa only [hpreviousIndex] using hpreviousRaw
  have hnextRaw := polygon.edge_cross_ne_zero_of_not_collinear
    hnoncollinear 1
  have hnextIndex : (1 : Fin (m + 3)) + 1 = 2 := by abel
  have hnext : kwComplexCross (polygon.edgeVector 1)
      (polygon.edgeVector 2) ≠ 0 := by
    simpa only [hnextIndex] using hnextRaw
  have hdiagonal : polygon.edgeVector 0 + polygon.edgeVector 1 ≠ 0 := by
    intro hzero
    have : polygon.edgeVector 1 = -polygon.edgeVector 0 := by
      linear_combination hzero
    apply hmiddle
    rw [this]
    simp [kwComplexCross]
    ring
  have hincomingDiagonal : kwComplexCross (polygon.edgeVector 0)
      (polygon.edgeVector 0 + polygon.edgeVector 1) =
        kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) := by
    rw [kwComplexCross_add_right, kwComplexCross_self, zero_add]
  have hdiagonalOutgoing :
      kwComplexCross (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 1) =
        kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) := by
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have houter := polygon.outerTurns_ne_pi_of_diagonalIsClean hm hear.1
  let previous := (Complex.arg (polygon.edgeVector (-1)) : Real.Angle)
  let incoming := (Complex.arg (polygon.edgeVector 0) : Real.Angle)
  let diagonal :=
    (Complex.arg (polygon.edgeVector 0 + polygon.edgeVector 1) : Real.Angle)
  let outgoing := (Complex.arg (polygon.edgeVector 1) : Real.Angle)
  let next := (Complex.arg (polygon.edgeVector 2) : Real.Angle)
  have hleftCases : kwAngleTurnNoWrap previous incoming diagonal ∨
      kwAngleTurnWrap previous incoming diagonal := by
    apply kwAngleTurnNoWrap_or_wrap
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero
        (polygon.edgeVector_ne_zero (-1)) (polygon.edgeVector_ne_zero 0)
        hprevious
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero
        (polygon.edgeVector_ne_zero 0) hdiagonal
        (hincomingDiagonal.symm ▸ hmiddle)
    · exact houter.1
  have hrightCases : kwAngleTurnNoWrap diagonal outgoing next ∨
      kwAngleTurnWrap diagonal outgoing next := by
    apply kwAngleTurnNoWrap_or_wrap
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero hdiagonal
        (polygon.edgeVector_ne_zero 1)
        (hdiagonalOutgoing.symm ▸ hmiddle)
    · exact kw_angle_sub_ne_pi_of_cross_ne_zero
        (polygon.edgeVector_ne_zero 1) (polygon.edgeVector_ne_zero 2) hnext
    · exact houter.2
  let phasePrevious : Fin (m + 3) := ⟨m + 1 + 1, by omega⟩
  have hphasePrevious : phasePrevious = (-1 : Fin (m + 3)) := by
    apply Fin.ext
    simp [phasePrevious, Fin.val_neg]
  dsimp only [KWFiniteSimplePolygon.VertexOneStrictParityEar]
  refine ⟨hear.1, hmiddle, ?_⟩
  rcases hleftCases with hleft | hleft <;>
      rcases hrightCases with hright | hright
  · exact Or.inl ⟨hleft, hright⟩
  · exfalso
    have hmixed := kwVectorTurnPhase_ear_splice_of_mixedParity
      (polygon.edgeVector (-1)) (polygon.edgeVector 0)
      (polygon.edgeVector 1) (polygon.edgeVector 2)
      (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
      hmiddle (Or.inl ⟨hleft, hright⟩)
    have hlocal : kwVectorTurnPhase (polygon.edgeVector phasePrevious)
          (polygon.edgeVector 0) *
        kwVectorTurnPhase (polygon.edgeVector 0) (polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 1) (polygon.edgeVector 2) =
      kwVectorTurnPhase (polygon.edgeVector phasePrevious)
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2) := by
      simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
        List.getLast_ofFn, hm, phasePrevious] using hear.2
    rw [hphasePrevious] at hlocal
    have hneg := hlocal.symm.trans hmixed
    have hzero : kwVectorTurnPhase (polygon.edgeVector (-1))
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2) = 0 := by
      linear_combination (1 / 2 : ℂ) * hneg
    exact (mul_ne_zero (kwVectorTurnPhase_ne_zero _ _)
      (kwVectorTurnPhase_ne_zero _ _)) hzero
  · exfalso
    have hmixed := kwVectorTurnPhase_ear_splice_of_mixedParity
      (polygon.edgeVector (-1)) (polygon.edgeVector 0)
      (polygon.edgeVector 1) (polygon.edgeVector 2)
      (polygon.edgeVector_ne_zero 0) (polygon.edgeVector_ne_zero 1)
      hmiddle (Or.inr ⟨hleft, hright⟩)
    have hlocal : kwVectorTurnPhase (polygon.edgeVector phasePrevious)
          (polygon.edgeVector 0) *
        kwVectorTurnPhase (polygon.edgeVector 0) (polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 1) (polygon.edgeVector 2) =
      kwVectorTurnPhase (polygon.edgeVector phasePrevious)
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2) := by
      simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
        List.getLast_ofFn, hm, phasePrevious] using hear.2
    rw [hphasePrevious] at hlocal
    have hneg := hlocal.symm.trans hmixed
    have hzero : kwVectorTurnPhase (polygon.edgeVector (-1))
          (polygon.edgeVector 0 + polygon.edgeVector 1) *
        kwVectorTurnPhase (polygon.edgeVector 0 + polygon.edgeVector 1)
          (polygon.edgeVector 2) = 0 := by
      linear_combination (1 / 2 : ℂ) * hneg
    exact (mul_ne_zero (kwVectorTurnPhase_ne_zero _ _)
      (kwVectorTurnPhase_ne_zero _ _)) hzero
  · exact Or.inr ⟨hleft, hright⟩

theorem KWFiniteSimplePolygon.vertexOneStrictParityEar_iff_geometricEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    polygon.VertexOneStrictParityEar ↔
      polygon.VertexOneGeometricEar hm := by
  constructor
  · exact polygon.vertexOneGeometricEar_of_strictParityEar hm
  · exact polygon.vertexOneStrictParityEar_of_geometricEar
      hm hnoncollinear


theorem KWFiniteSimplePolygon.exists_rotated_vertexOneGeometricEar_four
    (polygon : KWFiniteSimplePolygon 4)
    (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    ∃ r : Fin 4,
      (polygon.rotate r).VertexOneGeometricEar (by omega) := by
  obtain ⟨r, hear⟩ :=
    polygon.exists_rotated_vertexOneCrossEar_four hnoncollinear
  exact ⟨r,
    (polygon.rotate r).vertexOneDiagonalIsClean_four_of_crossEar hear,
    (polygon.rotate r).vertexOnePhaseEar_of_crossEar (by omega) hear⟩


theorem KWFiniteSimplePolygon.removable_of_geometricEar
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hear : polygon.VertexOneGeometricEar hm) :
    polygon.VertexOneRemovalIsSimple ∧ polygon.VertexOnePhaseEar hm := by
  exact ⟨polygon.vertexOneRemovalIsSimple_of_diagonalIsClean hear.1,
    hear.2⟩


theorem KWFiniteSimplePolygon.vertexOnePhaseEar_of_collinear
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hcol : Collinear ℝ
      ({polygon.vertex 0, polygon.vertex 1,
        polygon.vertex 2} : Set ℂ)) :
    polygon.VertexOnePhaseEar hm := by
  have hlocal := polygon.collinear_local_phase 0 hcol
  have hindex : (-1 : Fin (m + 3)) = Fin.last (m + 2) := by
    apply Fin.ext
    simp [Fin.val_neg]
  simp only [zero_sub, zero_add] at hlocal
  rw [hindex] at hlocal
  simpa [KWFiniteSimplePolygon.VertexOnePhaseEar, List.ofFn_succ,
    List.getLast_ofFn, hm] using hlocal


theorem KWFiniteSimplePolygon.exists_removable_of_exists_collinear
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hcol : ∃ i : Fin (m + 3), Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    ∃ r : Fin (m + 3),
      (polygon.rotate r).VertexOneRemovalIsSimple ∧
        (polygon.rotate r).VertexOnePhaseEar hm := by
  obtain ⟨i, hi⟩ := hcol
  refine ⟨i, ?_⟩
  have hrot : Collinear ℝ
      ({(polygon.rotate i).vertex 0, (polygon.rotate i).vertex 1,
        (polygon.rotate i).vertex 2} : Set ℂ) := by
    simpa [KWFiniteSimplePolygon.rotate, add_comm] using hi
  have hbetween :=
    (polygon.rotate i).consecutive_wbtw_of_collinear 0 hrot
  constructor
  · exact (polygon.rotate i).vertexOneRemovalIsSimple_of_between hbetween
  · exact (polygon.rotate i).vertexOnePhaseEar_of_collinear hm hrot


theorem KWFiniteSimplePolygon.exists_removable_of_noncollinear_case
    (hgeneric : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  intro m hm polygon
  by_cases hcol : ∃ i : Fin (m + 3), Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)
  · exact polygon.exists_removable_of_exists_collinear hm hcol
  · apply hgeneric m hm polygon
    simpa only [not_exists] using hcol


theorem KWFiniteSimplePolygon.exists_removable_of_geometricEar_case
    (hgeneric : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar hm) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  apply KWFiniteSimplePolygon.exists_removable_of_noncollinear_case
  intro m hm polygon hnoncollinear
  obtain ⟨r, hear⟩ := hgeneric m hm polygon hnoncollinear
  exact ⟨r, (polygon.rotate r).removable_of_geometricEar hm hear⟩


theorem KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
    (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar (by omega)) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  apply KWFiniteSimplePolygon.exists_removable_of_geometricEar_case
  intro m hm polygon hnoncollinear
  rcases eq_or_lt_of_le hm with rfl | hmTwo
  · simpa using polygon.exists_rotated_vertexOneGeometricEar_four
      hnoncollinear
  · exact hgeneric m hmTwo polygon hnoncollinear


theorem KWFiniteSimplePolygon.exists_removable_of_alignedSideEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneAlignedSideEar) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  apply KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
  intro m hm polygon hnoncollinear
  obtain ⟨r, hear⟩ := hgeneric m hm polygon hnoncollinear
  refine ⟨r, (polygon.rotate r).vertexOneGeometricEar_of_alignedSideEar
    (by omega) ?_ hear⟩
  exact polygon.rotate_not_collinear hnoncollinear r


theorem KWFiniteSimplePolygon.exists_removable_of_strictParityEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneStrictParityEar) :
    ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm := by
  apply KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
  intro m hm polygon hnoncollinear
  obtain ⟨r, hear⟩ := hgeneric m hm polygon hnoncollinear
  exact ⟨r, (polygon.rotate r).vertexOneGeometricEar_of_strictParityEar
    (by omega) hear⟩


theorem kwVectorPhasePath_contract_ear
    (previous incoming outgoing next : ℂ) (tail : List ℂ)
    (hp : previous ≠ 0) (hi : incoming ≠ 0)
    (ho : outgoing ≠ 0) (hn : next ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hrightTurn :
      (Complex.arg next : Real.Angle) -
        (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
    (hleft :
      (0 < kwComplexCross previous incoming ∧
          0 < kwComplexCross previous (incoming + outgoing)) ∨
        (kwComplexCross previous incoming < 0 ∧
          kwComplexCross previous (incoming + outgoing) < 0))
    (hright :
      (0 < kwComplexCross (incoming + outgoing) outgoing ∧
          0 < kwComplexCross (incoming + outgoing) next) ∨
        (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
          kwComplexCross (incoming + outgoing) next < 0)) :
    kwVectorPhasePath (previous :: incoming :: outgoing :: next :: tail) =
      kwVectorPhasePath
        (previous :: (incoming + outgoing) :: next :: tail) := by
  simp only [kwVectorPhasePath_cons_cons]
  have hlocal := kwVectorTurnPhase_ear_splice
    previous incoming outgoing next hp hi ho hn hmiddle hrightTurn hleft hright
  calc
    kwVectorTurnPhase previous incoming *
          (kwVectorTurnPhase incoming outgoing *
            (kwVectorTurnPhase outgoing next *
              kwVectorPhasePath (next :: tail))) =
        (kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next) *
          kwVectorPhasePath (next :: tail) := by ring
    _ = (kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next) *
        kwVectorPhasePath (next :: tail) := by rw [hlocal]
    _ = kwVectorTurnPhase previous (incoming + outgoing) *
        (kwVectorTurnPhase (incoming + outgoing) next *
          kwVectorPhasePath (next :: tail)) := by ring


theorem kwVectorPhasePath_contract_of_local
    (previous incoming outgoing next : ℂ) (tail : List ℂ)
    (hlocal :
      kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next =
        kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next) :
    kwVectorPhasePath (previous :: incoming :: outgoing :: next :: tail) =
      kwVectorPhasePath
        (previous :: (incoming + outgoing) :: next :: tail) := by
  simp only [kwVectorPhasePath_cons_cons]
  calc
    kwVectorTurnPhase previous incoming *
          (kwVectorTurnPhase incoming outgoing *
            (kwVectorTurnPhase outgoing next *
              kwVectorPhasePath (next :: tail))) =
        (kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next) *
          kwVectorPhasePath (next :: tail) := by ring
    _ = (kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next) *
        kwVectorPhasePath (next :: tail) := by rw [hlocal]
    _ = kwVectorTurnPhase previous (incoming + outgoing) *
        (kwVectorTurnPhase (incoming + outgoing) next *
          kwVectorPhasePath (next :: tail)) := by ring


theorem kwVectorPhaseCycle_contract_ear
    (previous incoming outgoing next : ℂ) (tail : List ℂ)
    (hp : previous ≠ 0) (hi : incoming ≠ 0)
    (ho : outgoing ≠ 0) (hn : next ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hrightTurn :
      (Complex.arg next : Real.Angle) -
        (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
    (hleft :
      (0 < kwComplexCross previous incoming ∧
          0 < kwComplexCross previous (incoming + outgoing)) ∨
        (kwComplexCross previous incoming < 0 ∧
          kwComplexCross previous (incoming + outgoing) < 0))
    (hright :
      (0 < kwComplexCross (incoming + outgoing) outgoing ∧
          0 < kwComplexCross (incoming + outgoing) next) ∨
        (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
          kwComplexCross (incoming + outgoing) next < 0)) :
    kwVectorPhaseCycle (previous :: incoming :: outgoing :: next :: tail) =
      kwVectorPhaseCycle
        (previous :: (incoming + outgoing) :: next :: tail) := by
  simp only [kwVectorPhaseCycle_cons]
  rw [kwVectorPhasePath_contract_ear previous incoming outgoing next tail
    hp hi ho hn hmiddle hrightTurn hleft hright]
  simp


theorem kwVectorPhaseCycle_contract_of_local
    (previous incoming outgoing next : ℂ) (tail : List ℂ)
    (hlocal :
      kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next =
        kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next) :
    kwVectorPhaseCycle (previous :: incoming :: outgoing :: next :: tail) =
      kwVectorPhaseCycle
        (previous :: (incoming + outgoing) :: next :: tail) := by
  simp only [kwVectorPhaseCycle_cons]
  rw [kwVectorPhasePath_contract_of_local
    previous incoming outgoing next tail hlocal]
  simp


end StatMech.FrontierA
