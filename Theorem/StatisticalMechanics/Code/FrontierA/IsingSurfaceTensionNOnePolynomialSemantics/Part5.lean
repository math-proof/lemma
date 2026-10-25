/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOnePolynomialSemantics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode.Part2
import Std.Data.TreeMap.Lemmas
import Std.Data.DTreeMap.Internal.Lemmas
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part4
open Finset
open Std
open scoped Std.DTreeMap.Internal.Impl


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

theorem shiftedTermListSum (C D : Real) (t : BiTerm) :
    ((shiftedTermExpansion t).map (BiTerm.eval C D)).sum =
      (t.coeff : Real) * (1 + C) ^ Int.toNat t.ex *
        (1 + D) ^ Int.toNat t.ey := by
  unfold shiftedTermExpansion
  have hinner (a : Nat) :
      (((List.range (Int.toNat t.ey + 1)).map fun b =>
        { ex := (a : Int), ey := (b : Int),
          coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
            ((Int.toNat t.ey).choose b : Int) }).map
          (BiTerm.eval C D)).sum =
        (t.coeff : Real) * (Int.toNat t.ex).choose a * C ^ a *
          (1 + D) ^ Int.toNat t.ey := by
    rw [← binomialListSum D (Int.toNat t.ey)]
    have hbs (bs : List Nat) :
        ((bs.map fun b =>
          { ex := (a : Int), ey := (b : Int),
            coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
              ((Int.toNat t.ey).choose b : Int) }).map
            (BiTerm.eval C D)).sum =
          (t.coeff : Real) * (Int.toNat t.ex).choose a * C ^ a *
            ((bs.map fun b =>
              ((Int.toNat t.ey).choose b : Real) * D ^ b).sum) := by
      induction bs with
      | nil => simp
      | cons b bs ih =>
          simp only [List.map_cons, List.sum_cons] at ih ⊢
          rw [ih]
          unfold BiTerm.eval
          simp only [Int.cast_mul, Int.cast_natCast, zpow_natCast]
          ring
    exact hbs (List.range (Int.toNat t.ey + 1))
  have houter (as : List Nat) :
      ((as.flatMap fun a =>
        (List.range (Int.toNat t.ey + 1)).map fun b =>
          { ex := (a : Int), ey := (b : Int),
            coeff := t.coeff * ((Int.toNat t.ex).choose a : Int) *
              ((Int.toNat t.ey).choose b : Int) }).map
          (BiTerm.eval C D)).sum =
        (t.coeff : Real) *
          ((as.map fun a =>
            ((Int.toNat t.ex).choose a : Real) * C ^ a).sum) *
          (1 + D) ^ Int.toNat t.ey := by
    induction as with
    | nil => simp
    | cons a as ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons, hinner, ih]
        ring
  rw [houter]
  rw [binomialListSum]

theorem BiPoly.eval_shiftToOne
    (q : BiPoly) (C D : Real)
    (hexp : ∀ t ∈ q.terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey) :
    q.shiftToOne.eval C D = q.eval (1 + C) (1 + D) := by
  have hlist : ∀ qs : List BiTerm,
      (∀ t ∈ qs, 0 ≤ t.ex ∧ 0 ≤ t.ey) ->
      (((qs.flatMap shiftedTermExpansion).map (BiTerm.eval C D)).sum) =
        (qs.map (BiTerm.eval (1 + C) (1 + D))).sum := by
    intro qs
    induction qs with
    | nil => intro hqs; simp
    | cons t ts ih =>
        intro hqs
        have ht := hqs t (by simp)
        have hts : ∀ s ∈ ts, 0 ≤ s.ex ∧ 0 ≤ s.ey := by
          intro s hs
          exact hqs s (by simp [hs])
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons]
        rw [shiftedTermListSum, ih hts]
        have hx : (1 + C) ^ Int.toNat t.ex = (1 + C) ^ t.ex := by
          rw [← zpow_natCast]
          rw [Int.toNat_of_nonneg ht.1]
        have hy : (1 + D) ^ Int.toNat t.ey = (1 + D) ^ t.ey := by
          rw [← zpow_natCast]
          rw [Int.toNat_of_nonneg ht.2]
        rw [hx, hy]
        rfl
  rw [BiPoly.shiftToOne, BiPoly.eval_ofTerms]
  unfold BiPoly.eval
  simpa only [shiftedTermExpansion] using
    hlist q.terms hexp

theorem BiPoly.eval_shiftedQuotientPolyOf
    (p : BiPoly) (C D : Real)
    (hexp : ∀ t ∈ (quotientPolyOf p).terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey) :
    (shiftedQuotientPolyOf p).eval C D =
      (quotientPolyOf p).eval (1 + C) (1 + D) := by
  exact BiPoly.eval_shiftToOne (quotientPolyOf p) C D hexp

theorem BiPoly.eval_nonneg_of_coeff_nonneg
    (p : BiPoly) (X Y : Real) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hcoeff : ∀ t ∈ p.terms, 0 ≤ t.coeff) :
    0 ≤ p.eval X Y := by
  unfold BiPoly.eval
  have hlist : ∀ ts : List BiTerm,
      (∀ t ∈ ts, 0 ≤ t.coeff) ->
      0 ≤ (ts.map (BiTerm.eval X Y)).sum := by
    intro ts
    induction ts with
    | nil => intro hts; simp
    | cons t ts ih =>
        intro hts
        simp only [List.map_cons, List.sum_cons]
        apply add_nonneg
        · unfold BiTerm.eval
          have hct : 0 ≤ t.coeff := hts t (by simp)
          have hc : (0 : Real) ≤ (t.coeff : Real) := by
            exact_mod_cast hct
          exact mul_nonneg
            (mul_nonneg hc (zpow_nonneg hX t.ex))
            (zpow_nonneg hY t.ey)
        · apply ih
          intro s hs
          exact hts s (by simp [hs])
  exact hlist p.terms hcoeff

theorem eval_shiftedQuotientPolyOf_nonneg_of_coefficientCertificate
    (p : BiPoly) (C D : Real) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcert : coefficientCertificateOf p = true) :
    0 ≤ (shiftedQuotientPolyOf p).eval C D := by
  unfold coefficientCertificateOf at hcert
  apply BiPoly.eval_nonneg_of_coeff_nonneg _ C D hC hD
  intro t ht
  have hall := List.all_eq_true.mp hcert
  have h := hall t ht
  simpa using h

theorem eval_quotientPolyOf_nonneg_of_coefficientCertificate
    (p : BiPoly) (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hexp : ∀ t ∈ (quotientPolyOf p).terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey)
    (hcert : coefficientCertificateOf p = true) :
    0 ≤ (quotientPolyOf p).eval X Y := by
  have hnonneg :=
    eval_shiftedQuotientPolyOf_nonneg_of_coefficientCertificate p
      (X - 1) (Y - 1) (sub_nonneg.mpr hX) (sub_nonneg.mpr hY) hcert
  rw [BiPoly.eval_shiftedQuotientPolyOf p (X - 1) (Y - 1) hexp]
    at hnonneg
  have hx : 1 + (X - 1) = X := by ring
  have hy : 1 + (Y - 1) = Y := by ring
  rw [hx, hy] at hnonneg
  exact hnonneg

theorem BiPoly.eval_mapExponent_add
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0)
    (ax ay : Int) :
    (p.mapExponent fun ex ey => (ex + ax, ey + ay)).eval X Y =
      p.eval X Y * X ^ ax * Y ^ ay := by
  rw [BiPoly.eval_mapExponent]
  unfold BiPoly.eval
  induction p.terms with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, zpow_add₀ hX, zpow_add₀ hY]
      unfold BiTerm.eval
      ring

theorem eval_clearedSkewPolyOf_eq_scaled_neg_skew
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0) :
    (clearedSkewPolyOf p).eval X Y =
      -(reflectedVarianceSkewPolyOf p).eval X Y * X ^ (-17 : Int) *
        Y ^ (17 : Int) := by
  unfold clearedSkewPolyOf
  change ((-(reflectedVarianceSkewPolyOf p)).mapExponent
    fun ex ey => (ex + (-17 : Int), ey + (17 : Int))).eval X Y = _
  rw [BiPoly.eval_mapExponent_add _ X Y hX hY, BiPoly.eval_neg]

theorem eval_clearedSkewPolyOf_nonneg_of_certificate
    (p : BiPoly) (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hexp : ∀ t ∈ (quotientPolyOf p).terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey)
    (hcert : certificateOf p = true) :
    0 ≤ (clearedSkewPolyOf p).eval X Y := by
  unfold certificateOf at hcert
  have hc := Bool.and_eq_true_iff.mp hcert
  have hX0 : X ≠ 0 := ne_of_gt (_root_.lt_of_lt_of_le zero_lt_one hX)
  have hY0 : Y ≠ 0 := ne_of_gt (_root_.lt_of_lt_of_le zero_lt_one hY)
  have hq := eval_quotientPolyOf_nonneg_of_coefficientCertificate
    p X Y hX hY hexp hc.2
  have hfactor :=
    eval_clearedSkewPolyOf_eq_factors_of_remainderCertificate
      p X Y hX0 hY0 hc.1
  rw [hfactor]
  have hxf : 0 ≤ X ^ 2 - 1 := by
    calc
      0 ≤ (X - 1) * (X + 1) := mul_nonneg (sub_nonneg.mpr hX)
        (add_nonneg (zero_le_one.trans hX) zero_le_one)
      _ = X ^ 2 - 1 := by ring
  have hyf : 0 ≤ Y ^ 2 - 1 := by
    calc
      0 ≤ (Y - 1) * (Y + 1) := mul_nonneg (sub_nonneg.mpr hY)
        (add_nonneg (zero_le_one.trans hY) zero_le_one)
      _ = Y ^ 2 - 1 := by ring
  exact mul_nonneg (mul_nonneg hq hxf) hyf

theorem eval_reflectedVarianceSkewPolyOf_nonpos_of_certificate
    (p : BiPoly) (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hexp : ∀ t ∈ (quotientPolyOf p).terms,
      0 ≤ t.ex ∧ 0 ≤ t.ey)
    (hcert : certificateOf p = true) :
    (reflectedVarianceSkewPolyOf p).eval X Y ≤ 0 := by
  have hXpos : 0 < X := _root_.lt_of_lt_of_le zero_lt_one hX
  have hYpos : 0 < Y := _root_.lt_of_lt_of_le zero_lt_one hY
  have hc := eval_clearedSkewPolyOf_nonneg_of_certificate
    p X Y hX hY hexp hcert
  rw [eval_clearedSkewPolyOf_eq_scaled_neg_skew p X Y
    hXpos.ne' hYpos.ne'] at hc
  rw [mul_assoc] at hc
  have hscale : 0 < X ^ (-17 : Int) * Y ^ (17 : Int) :=
    mul_pos (zpow_pos hXpos _) (zpow_pos hYpos _)
  have hneg : 0 ≤ -(reflectedVarianceSkewPolyOf p).eval X Y :=
    (mul_nonneg_iff_of_pos_right hscale).mp hc
  linarith


theorem eval_reflectedVarianceSkewPolyOf_nonpos_of_explicit_factor
    (p q : BiPoly) (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hfactor : (clearedSkewPolyOf p).eval X Y =
      q.eval X Y * (X ^ 2 - 1) * (Y ^ 2 - 1))
    (hq : 0 ≤ q.eval X Y) :
    (reflectedVarianceSkewPolyOf p).eval X Y ≤ 0 := by
  have hXpos : 0 < X := _root_.lt_of_lt_of_le zero_lt_one hX
  have hYpos : 0 < Y := _root_.lt_of_lt_of_le zero_lt_one hY
  have hxf : 0 ≤ X ^ 2 - 1 := by
    calc
      0 ≤ (X - 1) * (X + 1) := mul_nonneg (sub_nonneg.mpr hX)
        (add_nonneg (zero_le_one.trans hX) zero_le_one)
      _ = X ^ 2 - 1 := by ring
  have hyf : 0 ≤ Y ^ 2 - 1 := by
    calc
      0 ≤ (Y - 1) * (Y + 1) := mul_nonneg (sub_nonneg.mpr hY)
        (add_nonneg (zero_le_one.trans hY) zero_le_one)
      _ = Y ^ 2 - 1 := by ring
  have hc : 0 ≤ (clearedSkewPolyOf p).eval X Y := by
    rw [hfactor]
    exact mul_nonneg (mul_nonneg hq hxf) hyf
  rw [eval_clearedSkewPolyOf_eq_scaled_neg_skew p X Y
    hXpos.ne' hYpos.ne'] at hc
  rw [mul_assoc] at hc
  have hscale : 0 < X ^ (-17 : Int) * Y ^ (17 : Int) :=
    mul_pos (zpow_pos hXpos _) (zpow_pos hYpos _)
  have hneg : 0 ≤ -(reflectedVarianceSkewPolyOf p).eval X Y :=
    (mul_nonneg_iff_of_pos_right hscale).mp hc
  linarith

end StatMech.FrontierA.NOneSymmetricMeanCertificate
