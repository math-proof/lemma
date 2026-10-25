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


namespace StatMech.FrontierA

theorem kw_sbtw_iff_mem_openSegment {x y z : ℂ} (hxz : x ≠ z) :
    Sbtw ℝ x y z ↔ y ∈ openSegment ℝ x z := by
  constructor
  · intro h
    rw [openSegment_eq_image_lineMap]
    exact h.mem_image_Ioo
  · intro h
    rw [openSegment_eq_image_lineMap] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact sbtw_lineMap_iff.mpr ⟨hxz, ht⟩


theorem kw_sbtw_eq_or_sbtw_or_sbtw {a b c z : ℂ}
    (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c)
    (hbetween : Wbtw ℝ a b c) (hz : Sbtw ℝ a z c) :
    z = b ∨ Sbtw ℝ a z b ∨ Sbtw ℝ b z c := by
  have hbline : b ∈ Set.range (AffineMap.lineMap a c : ℝ → ℂ) := by
    rcases hbetween with ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  have hzmem : z ∈ openSegment ℝ a c :=
    (kw_sbtw_iff_mem_openSegment hac).mp hz
  rcases openSegment_subset_union a c hbline hzmem with hzB | hzleft | hzright
  · exact Or.inl hzB
  · exact Or.inr <| Or.inl <|
      (kw_sbtw_iff_mem_openSegment hab).mpr hzleft
  · exact Or.inr <| Or.inr <|
      (kw_sbtw_iff_mem_openSegment hbc).mpr hzright

theorem kwComplexCross_add_right (a b c : ℂ) :
    kwComplexCross a (b + c) =
      kwComplexCross a b + kwComplexCross a c := by
  unfold kwComplexCross
  simp only [Complex.add_re, Complex.add_im]
  ring

theorem kwComplexCross_sub_right (a b c : ℂ) :
    kwComplexCross a (b - c) =
      kwComplexCross a b - kwComplexCross a c := by
  unfold kwComplexCross
  simp only [Complex.sub_re, Complex.sub_im]
  ring

theorem kwComplexCross_mul_real_left (r : ℝ) (a b : ℂ) :
    kwComplexCross ((r : ℂ) * a) b = r * kwComplexCross a b := by
  unfold kwComplexCross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem kwComplexCross_mul_real_right (r : ℝ) (a b : ℂ) :
    kwComplexCross a ((r : ℂ) * b) = r * kwComplexCross a b := by
  unfold kwComplexCross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

@[simp] theorem kwComplexCross_self (a : ℂ) :
    kwComplexCross a a = 0 := by
  unfold kwComplexCross
  ring

theorem kwComplexCross_swap (a b : ℂ) :
    kwComplexCross a b = -kwComplexCross b a := by
  unfold kwComplexCross
  ring

@[simp] theorem kwComplexCross_neg_right (a b : ℂ) :
    kwComplexCross a (-b) = -kwComplexCross a b := by
  unfold kwComplexCross
  simp
  ring


theorem kw_exists_common_sbtw_of_cross_opposite {A B C D : ℂ}
    (hAB : kwComplexCross (B - A) (C - A) *
        kwComplexCross (B - A) (D - A) < 0)
    (hCD : kwComplexCross (D - C) (A - C) *
        kwComplexCross (D - C) (B - C) < 0) :
    ∃ z : ℂ, Sbtw ℝ A z B ∧ Sbtw ℝ C z D := by
  let a := B - A
  let c := D - C
  let x := kwComplexCross c (A - C)
  let y := kwComplexCross a (C - A)
  let den := kwComplexCross a c
  have hABD : kwComplexCross a (D - A) = y + den := by
    dsimp only [a, c, y, den]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hCDB : kwComplexCross c (B - C) = x - den := by
    dsimp only [a, c, x, den]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hxy : y * (y + den) < 0 := by
    simpa only [a, y, hABD] using hAB
  have hxx : x * (x - den) < 0 := by
    simpa only [c, x, hCDB] using hCD
  have hden : den ≠ 0 := by
    intro hz
    rw [hz] at hxy
    norm_num at hxy
    nlinarith [sq_nonneg y]
  let t : ℝ := x / den
  let u : ℝ := -y / den
  have interval_div (v : ℝ) (hv : v * (v - den) < 0) :
      v / den ∈ Set.Ioo (0 : ℝ) 1 := by
    rcases lt_or_gt_of_ne hden with hdneg | hdpos
    · have hvneg : v < 0 := by
        by_contra hn
        have hv0 : 0 ≤ v := le_of_not_gt hn
        have hvd0 : 0 ≤ v - den := by linarith
        exact (not_lt_of_ge (mul_nonneg hv0 hvd0)) hv
      have hdv : den < v := by
        by_contra hn
        have hvd : v ≤ den := le_of_not_gt hn
        have hv0 : v ≤ 0 := le_trans hvd hdneg.le
        have hvd0 : v - den ≤ 0 := sub_nonpos.mpr hvd
        exact (not_lt_of_ge
          (mul_nonneg_of_nonpos_of_nonpos hv0 hvd0)) hv
      exact ⟨div_pos_of_neg_of_neg hvneg hdneg,
        (div_lt_one_of_neg hdneg).mpr hdv⟩
    · have hvpos : 0 < v := by
        by_contra hn
        have hv0 : v ≤ 0 := le_of_not_gt hn
        have hvd0 : v - den ≤ 0 := by linarith
        exact (not_lt_of_ge
          (mul_nonneg_of_nonpos_of_nonpos hv0 hvd0)) hv
      have hvd : v < den := by
        by_contra hn
        have hdv : den ≤ v := le_of_not_gt hn
        have hv0 : 0 ≤ v := le_trans hdpos.le hdv
        have hvd0 : 0 ≤ v - den := sub_nonneg.mpr hdv
        exact (not_lt_of_ge (mul_nonneg hv0 hvd0)) hv
      exact ⟨div_pos hvpos hdpos, (div_lt_one hdpos).mpr hvd⟩
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := interval_div x hxx
  have hu : u ∈ Set.Ioo (0 : ℝ) 1 := by
    apply interval_div (-y)
    nlinarith [hxy]
  let w : ℂ := (t : ℂ) * a - (u : ℂ) * c - (C - A)
  have haw : kwComplexCross a w = 0 := by
    calc
      kwComplexCross a w = -(u * den) - y := by
        dsimp only [w]
        rw [kwComplexCross_sub_right, kwComplexCross_sub_right,
          kwComplexCross_mul_real_right, kwComplexCross_mul_real_right,
          kwComplexCross_self]
        dsimp only [den, y]
        ring
      _ = 0 := by
        dsimp only [u]
        field_simp [hden]
        ring
  have hcw : kwComplexCross c w = 0 := by
    calc
      kwComplexCross c w = -(t * den) + x := by
        dsimp only [w]
        rw [kwComplexCross_sub_right, kwComplexCross_sub_right,
          kwComplexCross_mul_real_right, kwComplexCross_mul_real_right,
          kwComplexCross_self, kwComplexCross_swap]
        have hneg : C - A = -(A - C) := by ring
        rw [hneg, kwComplexCross_neg_right]
        dsimp only [den, x]
        ring
      _ = 0 := by
        dsimp only [t]
        field_simp [hden]
        ring
  have hwre : w.re = 0 := by
    have hprod : den * w.re = 0 := by
      dsimp only [den]
      unfold kwComplexCross at haw hcw ⊢
      linear_combination c.re * haw - a.re * hcw
    exact (mul_eq_zero.mp hprod).resolve_left hden
  have hwim : w.im = 0 := by
    have hprod : den * w.im = 0 := by
      dsimp only [den]
      unfold kwComplexCross at haw hcw ⊢
      linear_combination c.im * haw - a.im * hcw
    exact (mul_eq_zero.mp hprod).resolve_left hden
  have hw : w = 0 := Complex.ext hwre hwim
  have hAC : C - A = (t : ℂ) * a - (u : ℂ) * c := by
    dsimp only [w] at hw
    rw [sub_eq_zero] at hw
    exact hw.symm
  have hline : AffineMap.lineMap A B t = AffineMap.lineMap C D u := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    change (t : ℂ) * (B - A) + A = (u : ℂ) * (D - C) + C
    rw [show B - A = a by rfl, show D - C = c by rfl]
    rw [show C = (C - A) + A by ring, hAC]
    ring
  refine ⟨AffineMap.lineMap A B t, ?_, ?_⟩
  · exact sbtw_lineMap_iff.mpr ⟨(by
      intro hab
      subst B
      simp [kwComplexCross] at hAB), ht⟩
  · rw [hline]
    exact sbtw_lineMap_iff.mpr ⟨(by
      intro hcd
      subst D
      simp [kwComplexCross] at hCD), hu⟩


theorem kwComplexCross_eq_zero_of_sbtw {A B C : ℂ}
    (h : Sbtw ℝ A B C) :
    kwComplexCross (C - A) (B - A) = 0 := by
  obtain ⟨t, ht, htEq⟩ := h.mem_image_Ioo
  have heq := congrArg
    (fun w : ℂ ↦ kwComplexCross (C - A) (w - A)) htEq
  rw [AffineMap.lineMap_apply] at heq
  simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right,
    Complex.real_smul, kwComplexCross_mul_real_right,
    kwComplexCross_self, mul_zero] at heq
  exact heq.symm


theorem kw_openSegments_disjoint_of_common_left_cross_ne
    {A B C : ℂ} (hcross : kwComplexCross (B - A) (C - A) ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ A z B} {z : ℂ | Sbtw ℝ A z C} := by
  rw [Set.disjoint_left]
  intro z hzAB hzAC
  obtain ⟨t, ht, htEq⟩ := hzAB.mem_image_Ioo
  obtain ⟨u, hu, huEq⟩ := hzAC.mem_image_Ioo
  have heq : AffineMap.lineMap A B t = AffineMap.lineMap A C u :=
    htEq.trans huEq.symm
  have hcrossEq := congrArg
    (fun w : ℂ ↦ kwComplexCross (B - A) (w - A)) heq
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply] at hcrossEq
  simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right,
    Complex.real_smul] at hcrossEq
  rw [kwComplexCross_mul_real_right, kwComplexCross_mul_real_right,
    kwComplexCross_self, mul_zero] at hcrossEq
  exact hcross (mul_eq_zero.mp hcrossEq.symm |>.resolve_left hu.1.ne')


theorem kw_fourVector_crossEar
    (p a b q : ℂ) (hb : b ≠ 0) (hq : q ≠ 0)
    (hsum : p + a + b + q = 0)
    (hbq : kwComplexCross b q ≠ 0)
    (hsign :
      (0 < kwComplexCross p a ∧ 0 < kwComplexCross a b ∧
          0 < kwComplexCross q p) ∨
        (kwComplexCross p a < 0 ∧ kwComplexCross a b < 0 ∧
          kwComplexCross q p < 0)) :
    kwComplexCross a b ≠ 0 ∧
      (Complex.arg q : Real.Angle) - (Complex.arg b : Real.Angle) ≠
        (Real.pi : Real.Angle) ∧
      ((0 < kwComplexCross p a ∧
          0 < kwComplexCross p (a + b)) ∨
        (kwComplexCross p a < 0 ∧
          kwComplexCross p (a + b) < 0)) ∧
      ((0 < kwComplexCross (a + b) b ∧
          0 < kwComplexCross (a + b) q) ∨
        (kwComplexCross (a + b) b < 0 ∧
          kwComplexCross (a + b) q < 0)) := by
  have hpdiag : kwComplexCross p (a + b) = kwComplexCross q p := by
    have hre := congrArg Complex.re hsum
    have him := congrArg Complex.im hsum
    simp only [Complex.add_re, Complex.zero_re] at hre
    simp only [Complex.add_im, Complex.zero_im] at him
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    linear_combination p.re * him - p.im * hre
  have hdiagb : kwComplexCross (a + b) b = kwComplexCross a b := by
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hdiagq : kwComplexCross (a + b) q = kwComplexCross q p := by
    have hre := congrArg Complex.re hsum
    have him := congrArg Complex.im hsum
    simp only [Complex.add_re, Complex.zero_re] at hre
    simp only [Complex.add_im, Complex.zero_im] at him
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    linear_combination q.im * hre - q.re * him
  constructor
  · rcases hsign with h | h <;> nlinarith [h.2.1]
  constructor
  · exact kw_angle_sub_ne_pi_of_cross_ne_zero hb hq hbq
  constructor
  · rw [hpdiag]
    rcases hsign with h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr ⟨h.1, h.2.2⟩
  · rw [hdiagb, hdiagq]
    rcases hsign with h | h
    · exact Or.inl ⟨h.2.1, h.2.2⟩
    · exact Or.inr ⟨h.2.1, h.2.2⟩


end StatMech.FrontierA
