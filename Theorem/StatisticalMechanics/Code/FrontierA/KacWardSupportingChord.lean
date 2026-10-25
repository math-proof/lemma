/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardExtremeVertex
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment


namespace StatMech.FrontierA

theorem kw_eq_real_mul_of_cross_eq_zero {v w : ℂ} (hv : v ≠ 0)
    (hcross : kwComplexCross v w = 0) :
    w = ((kwComplexDot v w / Complex.normSq v : ℝ) : ℂ) * v := by
  have hnorm : Complex.normSq v ≠ 0 :=
    (Complex.normSq_pos.mpr hv).ne'
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [div_mul_eq_mul_div, eq_div_iff hnorm]
    rw [Complex.normSq_apply]
    unfold kwComplexCross at hcross
    unfold kwComplexDot
    linear_combination -v.im * hcross
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rw [div_mul_eq_mul_div, eq_div_iff hnorm]
    rw [Complex.normSq_apply]
    unfold kwComplexCross at hcross
    unfold kwComplexDot
    linear_combination v.re * hcross


theorem kw_lineMap_openSegments_overlap_endpoints_of_lt
    {A D z : ℂ} (hAD : A ≠ D) {x y : ℝ} (hxy : x < y)
    (hzAD : Sbtw ℝ A z D)
    (hzXY : Sbtw ℝ (AffineMap.lineMap A D x) z
      (AffineMap.lineMap A D y)) :
    Sbtw ℝ A (AffineMap.lineMap A D x) D ∨
      Sbtw ℝ A (AffineMap.lineMap A D y) D ∨
      Sbtw ℝ (AffineMap.lineMap A D x) A
        (AffineMap.lineMap A D y) ∨
      Sbtw ℝ (AffineMap.lineMap A D x) D
        (AffineMap.lineMap A D y) ∨
      (AffineMap.lineMap A D x = A ∧
        AffineMap.lineMap A D y = D) := by
  obtain ⟨t, ht, htEq⟩ := hzAD.mem_image_Ioo
  obtain ⟨u, hu, huEq⟩ := hzXY.mem_image_Ioo
  have hcoord : t = (1 - u) * x + u * y := by
    apply AffineMap.lineMap_injective ℝ hAD
    calc
      AffineMap.lineMap A D t = z := htEq
      _ = AffineMap.lineMap (AffineMap.lineMap A D x)
          (AffineMap.lineMap A D y) u := huEq.symm
      _ = AffineMap.lineMap A D ((1 - u) * x + u * y) := by
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          Complex.real_smul]
        push_cast
        ring
  have hxt : x < t := by nlinarith [hu.1, hu.2]
  have hty : t < y := by nlinarith [hu.1, hu.2]
  by_cases hx0 : 0 < x
  · exact Or.inl (sbtw_lineMap_iff.mpr
      ⟨hAD, hx0, by linarith [ht.2, hxt]⟩)
  by_cases hy1 : y < 1
  · exact Or.inr (Or.inl (sbtw_lineMap_iff.mpr
      ⟨hAD, by linarith [ht.1, hty], hy1⟩))
  have hxNonpos : x ≤ 0 := le_of_not_gt hx0
  have hyOne : 1 ≤ y := le_of_not_gt hy1
  by_cases hxNeg : x < 0
  · have hs : Sbtw ℝ x 0 y :=
      Sbtw.of_lt_of_lt hxNeg (by linarith [ht.1, hty])
    have hmapped : Sbtw ℝ (AffineMap.lineMap A D x)
        (AffineMap.lineMap A D (0 : ℝ)) (AffineMap.lineMap A D y) :=
      ((AffineMap.lineMap_injective ℝ hAD).sbtw_map_iff).mpr hs
    exact Or.inr (Or.inr (Or.inl (by simpa using hmapped)))
  have hxEq : x = 0 := le_antisymm hxNonpos (not_lt.mp hxNeg)
  by_cases hyGt : 1 < y
  · have hs : Sbtw ℝ x 1 y :=
      Sbtw.of_lt_of_lt (by linarith) hyGt
    have hmapped : Sbtw ℝ (AffineMap.lineMap A D x)
        (AffineMap.lineMap A D (1 : ℝ)) (AffineMap.lineMap A D y) :=
      ((AffineMap.lineMap_injective ℝ hAD).sbtw_map_iff).mpr hs
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hmapped))))
  have hyEq : y = 1 := le_antisymm (not_lt.mp hyGt) hyOne
  exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [hxEq, hyEq]))))


theorem kw_lineMap_openSegments_overlap_endpoints
    {A D z : ℂ} (hAD : A ≠ D) {x y : ℝ} (hxy : x ≠ y)
    (hzAD : Sbtw ℝ A z D)
    (hzXY : Sbtw ℝ (AffineMap.lineMap A D x) z
      (AffineMap.lineMap A D y)) :
    Sbtw ℝ A (AffineMap.lineMap A D x) D ∨
      Sbtw ℝ A (AffineMap.lineMap A D y) D ∨
      Sbtw ℝ (AffineMap.lineMap A D x) A
        (AffineMap.lineMap A D y) ∨
      Sbtw ℝ (AffineMap.lineMap A D x) D
        (AffineMap.lineMap A D y) ∨
      (AffineMap.lineMap A D x = A ∧
        AffineMap.lineMap A D y = D) ∨
      (AffineMap.lineMap A D x = D ∧
        AffineMap.lineMap A D y = A) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · rcases kw_lineMap_openSegments_overlap_endpoints_of_lt hAD hlt
      hzAD hzXY with hX | hY | hA | hD | hEq
    · exact Or.inl hX
    · exact Or.inr (Or.inl hY)
    · exact Or.inr (Or.inr (Or.inl hA))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hD)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hEq))))
  · rcases kw_lineMap_openSegments_overlap_endpoints_of_lt hAD hgt
      hzAD ((sbtw_comm).mpr hzXY) with hY | hX | hA | hD | hEq
    · exact Or.inr (Or.inl hY)
    · exact Or.inl hX
    · exact Or.inr (Or.inr (Or.inl ((sbtw_comm).mpr hA)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((sbtw_comm).mpr hD))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hEq.symm))))


theorem kw_openSegments_overlap_collinear_endpoints
    {A D X Y z : ℂ} (hAD : A ≠ D) (hXY : X ≠ Y)
    (hX : kwComplexCross (D - A) (X - A) = 0)
    (hY : kwComplexCross (D - A) (Y - A) = 0)
    (hzAD : Sbtw ℝ A z D) (hzXY : Sbtw ℝ X z Y) :
    Sbtw ℝ A X D ∨ Sbtw ℝ A Y D ∨ Sbtw ℝ X A Y ∨
      Sbtw ℝ X D Y ∨ (X = A ∧ Y = D) ∨ (X = D ∧ Y = A) := by
  let v := D - A
  let x := kwComplexDot v (X - A) / Complex.normSq v
  let y := kwComplexDot v (Y - A) / Complex.normSq v
  have hv : v ≠ 0 := sub_ne_zero.mpr hAD.symm
  have hXvec : X - A = (x : ℂ) * v := by
    exact kw_eq_real_mul_of_cross_eq_zero hv hX
  have hYvec : Y - A = (y : ℂ) * v := by
    exact kw_eq_real_mul_of_cross_eq_zero hv hY
  have hXline : AffineMap.lineMap A D x = X := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    rw [← hXvec]
    ring
  have hYline : AffineMap.lineMap A D y = Y := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    rw [← hYvec]
    ring
  have hxy : x ≠ y := by
    intro h
    apply hXY
    rw [← hXline, ← hYline, h]
  simpa only [hXline, hYline] using
    kw_lineMap_openSegments_overlap_endpoints hAD hxy hzAD
      (by simpa only [hXline, hYline] using hzXY)


theorem kw_cross_endpoints_eq_zero_of_intersect_of_nonneg
    {A D X Y z : ℂ}
    (hzAD : Sbtw ℝ A z D) (hzXY : Sbtw ℝ X z Y)
    (hX : 0 ≤ kwComplexCross (D - A) (X - A))
    (hY : 0 ≤ kwComplexCross (D - A) (Y - A)) :
    kwComplexCross (D - A) (X - A) = 0 ∧
      kwComplexCross (D - A) (Y - A) = 0 := by
  by_cases hXzero : kwComplexCross (D - A) (X - A) = 0
  · exact ⟨hXzero,
      kw_cross_right_eq_zero_of_openSegments_intersect_of_left_eq_zero
        hzAD hzXY hXzero⟩
  by_cases hYzero : kwComplexCross (D - A) (Y - A) = 0
  · exact ⟨kw_cross_left_eq_zero_of_openSegments_intersect_of_right_eq_zero
        hzAD hzXY hYzero, hYzero⟩
  have hprod := kw_cross_product_neg_of_openSegments_intersect
    hzAD hzXY hXzero hYzero
  exfalso
  exact (not_lt_of_ge (mul_nonneg hX hY)) hprod


end StatMech.FrontierA
