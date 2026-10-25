/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogSingularity


namespace StatMech.FrontierD

noncomputable section

theorem hasDerivAt_sixVertexBetheLogNormKernel
    {c x : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    HasDerivAt (sixVertexBetheLogNormKernel c)
      (sixVertexBetheLogNormDerivative c x) x := by
  let a := c ^ 2 - 1
  let A : Real → Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let B : Real → Real := fun y => 2 - 2 * Real.cos y
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : 0 < A x := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hB : 0 < B x := by
    dsimp [B]
    have hcos : Real.cos x < 1 := by
      rw [← Real.cos_abs, ← Real.cos_zero]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · exact le_rfl
      · exact abs_le.mpr hxIcc
      · exact abs_pos.mpr hx
    linarith
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add (a ^ 2 + 1)
      using 1 <;> ring
  have hBderiv : HasDerivAt B (2 * Real.sin x) x := by
    dsimp [B]
    convert (Real.hasDerivAt_cos x).const_mul (-2) |>.const_add 2
      using 1 <;> ring
  have hlogA := hAderiv.log hA.ne'
  have hlogB := hBderiv.log hB.ne'
  have hlog := (hlogA.sub hlogB).const_mul (1 / 2 : Real)
  unfold sixVertexBetheLogNormKernel sixVertexBetheLogNormDerivative
  dsimp [a, A, B] at hlog ⊢
  convert hlog using 1 <;> field_simp [hA.ne', hB.ne'] <;> ring

theorem abs_mul_sixVertexBetheLogNormDenominatorDerivative_le
    {x : Real} (hx : x ≠ 0) (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |x * (Real.sin x / (2 - 2 * Real.cos x))| ≤ Real.pi / 2 := by
  let u := x / 2
  have huIcc : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [u]
    constructor <;> linarith [hxIcc.1, hxIcc.2]
  have husin : 2 / Real.pi * |u| ≤ |Real.sin u| :=
    Real.mul_abs_le_abs_sin (abs_le.2 huIcc)
  have hu0 : u ≠ 0 := by dsimp [u]; exact div_ne_zero hx (by norm_num)
  have hsin0 : Real.sin u ≠ 0 := by
    intro h
    rw [h, abs_zero] at husin
    have : 0 < 2 / Real.pi * |u| := mul_pos (by positivity) (abs_pos.mpr hu0)
    linarith
  have hsin : Real.sin x = 2 * Real.sin u * Real.cos u := by
    rw [show x = 2 * u by dsimp [u]; ring, Real.sin_two_mul]
  have hden : 2 - 2 * Real.cos x = 4 * Real.sin u ^ 2 := by
    rw [show x = 2 * u by dsimp [u]; ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq u]
  rw [hden, hsin, abs_mul, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (show 0 ≤ (2 : Real) by norm_num)]
  rw [abs_mul, abs_of_nonneg (show 0 ≤ (4 : Real) by norm_num), abs_pow]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hucos : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
  have hux : |x| = 2 * |u| := by
    calc
      |x| = |2 * u| := by congr 1; dsimp [u]; ring
      _ = 2 * |u| := by rw [abs_mul]; norm_num
  have hsinLower : |x| / Real.pi ≤ |Real.sin u| := by
    calc
      |x| / Real.pi = 2 / Real.pi * |u| := by rw [hux]; ring
      _ ≤ |Real.sin u| := husin
  have hsinPos : 0 < |Real.sin u| := abs_pos.mpr hsin0
  rw [pow_two]
  have heq :
      |x| * (2 * |Real.sin u| * |Real.cos u| /
        (4 * (|Real.sin u| * |Real.sin u|))) =
      |x| * |Real.cos u| / (2 * |Real.sin u|) := by
    field_simp [hsinPos.ne']
    ring
  rw [heq, div_le_iff₀ (mul_pos (by positivity) hsinPos)]
  have hxnonneg : 0 ≤ |x| := abs_nonneg x
  have hxle : |x| ≤ Real.pi * |Real.sin u| := by
    simpa [mul_comm] using (div_le_iff₀ Real.pi_pos).mp hsinLower
  have hmul := mul_le_mul_of_nonneg_left hucos hxnonneg
  nlinarith

theorem abs_mul_sixVertexBetheLogNormDerivative_le
    {c x : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |x * sixVertexBetheLogNormDerivative c x| ≤
      Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2 := by
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : (a - 1) ^ 2 ≤ A := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x]
  have hApos : 0 < A := lt_of_lt_of_le (sq_pos_of_pos (sub_pos.mpr ha)) hA
  have hxabs : |x| ≤ Real.pi := abs_le.mpr hxIcc
  have hsabs : |Real.sin x| ≤ 1 := by
    exact abs_le.2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
  have hreg : |x * (-a * Real.sin x / A)| ≤
      Real.pi * a / (a - 1) ^ 2 := by
    rw [abs_mul, abs_div, abs_mul, abs_neg, abs_of_pos (zero_lt_one.trans ha),
      abs_of_pos hApos]
    rw [show |x| * (a * |Real.sin x| / A) =
      (|x| * a * |Real.sin x|) / A by ring]
    rw [div_le_div_iff₀ hApos (sq_pos_of_pos (sub_pos.mpr ha))]
    have hprod : |x| * |Real.sin x| ≤ Real.pi := by
      nlinarith [mul_le_mul hxabs hsabs (abs_nonneg (Real.sin x)) Real.pi_pos.le]
    have ha0 : 0 ≤ a := ha.le.trans' zero_le_one
    calc
      |x| * a * |Real.sin x| * (a - 1) ^ 2 =
          a * (|x| * |Real.sin x|) * (a - 1) ^ 2 := by ring
      _ ≤ a * Real.pi * (a - 1) ^ 2 := by gcongr
      _ ≤ a * Real.pi * A := by gcongr
      _ = Real.pi * a * A := by ring
  have hsing := abs_mul_sixVertexBetheLogNormDenominatorDerivative_le hx hxIcc
  unfold sixVertexBetheLogNormDerivative
  dsimp [a, A] at hreg ⊢
  calc
    |x * (-a * Real.sin x /
          (a ^ 2 + 1 + 2 * a * Real.cos x) -
        Real.sin x / (2 - 2 * Real.cos x))| ≤
        |x * (-a * Real.sin x /
          (a ^ 2 + 1 + 2 * a * Real.cos x))| +
        |x * (Real.sin x / (2 - 2 * Real.cos x))| := by
          rw [mul_sub]
          exact abs_sub _ _
    _ ≤ Real.pi * a / (a - 1) ^ 2 + Real.pi / 2 :=
      add_le_add hreg hsing
    _ = Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2 := by
      dsimp [a]
      ring

theorem abs_mul_sixVertexBetheLogNormDerivative_of_linearOffset
    {c C x f : Real} (hc : 2 < c) (hx : x ≠ 0)
    (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hf : |f| ≤ C * |x|) :
    |f * sixVertexBetheLogNormDerivative c x| ≤
      C * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi / 2) := by
  have hkernel := abs_mul_sixVertexBetheLogNormDerivative_le hc hx hxIcc
  have hxpos : 0 < |x| := abs_pos.mpr hx
  have hC : 0 ≤ C := by
    have hCx : 0 ≤ C * |x| := (abs_nonneg f).trans hf
    exact nonneg_of_mul_nonneg_left hCx hxpos
  rw [abs_mul]
  calc
    |f| * |sixVertexBetheLogNormDerivative c x| =
        (|f| / |x|) * |x * sixVertexBetheLogNormDerivative c x| := by
          rw [abs_mul]
          field_simp [hxpos.ne']
    _ ≤ C * |x * sixVertexBetheLogNormDerivative c x| := by
      gcongr
      exact (div_le_iff₀ hxpos).2 hf
    _ ≤ C * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 +
        Real.pi / 2) :=
      mul_le_mul_of_nonneg_left hkernel hC

end
end StatMech.FrontierD
