/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogUnregularization
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part2


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem sixVertexBetheDesingularizedLogObservable_eq
    {c x : Real} (hc : 2 < c) (hx : x ∈ Set.Ioo 0 Real.pi) :
    sixVertexBetheDesingularizedLogObservable c x =
      sixVertexBetheLogObservable c x + Real.log x := by
  rw [sixVertexBetheLogObservable_eq_logNormKernel hc hx]
  let a := c ^ 2 - 1
  let A := a ^ 2 + 1 + 2 * a * Real.cos x
  have hx0 : x ≠ 0 := hx.1.ne'
  have hhalf0 : x / 2 ≠ 0 := div_ne_zero hx0 (by norm_num)
  have hsinPos : 0 < Real.sin (x / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [hx.1]
    · nlinarith [hx.2, Real.pi_pos]
  have hsin0 : Real.sin (x / 2) ≠ 0 := hsinPos.ne'
  have hA : 0 < A := by
    have ha : 1 < a := by dsimp [a]; nlinarith
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hden : 2 - 2 * Real.cos x = 4 * Real.sin (x / 2) ^ 2 := by
    rw [Real.sin_sq_eq_half_sub]
    congr 1
    ring
  have hsinc : Real.sinc (x / 2) = Real.sin (x / 2) / (x / 2) :=
    Real.sinc_of_ne_zero hhalf0
  unfold sixVertexBetheDesingularizedLogObservable
    sixVertexBetheLogNormKernel
  dsimp [a, A]
  rw [hden, hsinc]
  have hxPos : 0 < x := hx.1
  rw [Real.log_div hsin0 hhalf0]
  rw [Real.log_div hx0 (by norm_num : (2 : Real) ≠ 0)]
  rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0)
    (pow_ne_zero 2 hsin0), Real.log_pow]
  rw [show Real.log (4 : Real) = 2 * Real.log 2 by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num]
  ring

theorem sixVertexBetheDesingularizedLogObservable_zero
    {c : Real} (hc : 2 < c) :
    sixVertexBetheDesingularizedLogObservable c 0 = Real.log (c ^ 2) := by
  have hc0 : c ≠ 0 := by linarith
  unfold sixVertexBetheDesingularizedLogObservable
  dsimp
  simp only [Real.cos_zero, zero_div, Real.sinc_zero, Real.log_one, sub_zero]
  rw [show (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * 1 =
    (c ^ 2) ^ 2 by ring]
  rw [Real.log_pow]
  ring

theorem sixVertexBetheDesingularizedLogObservable_pi
    {c : Real} (hc : 2 < c) :
    sixVertexBetheDesingularizedLogObservable c Real.pi =
      Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) +
        Real.log Real.pi := by
  have hd : 0 < c ^ 2 - 2 := by nlinarith [sq_nonneg (c - 2)]
  have hpi2 : Real.pi / 2 ≠ 0 := by positivity
  have hsinc : Real.sinc (Real.pi / 2) = 2 / Real.pi := by
    rw [Real.sinc_of_ne_zero hpi2, Real.sin_pi_div_two]
    field_simp [Real.pi_ne_zero]
  unfold sixVertexBetheDesingularizedLogObservable
  dsimp
  rw [Real.cos_pi, hsinc]
  rw [show (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * -1 =
    (c ^ 2 - 2) ^ 2 by ring]
  rw [Real.log_pow, Real.log_div (by norm_num : (2 : Real) ≠ 0)
    Real.pi_ne_zero]
  rw [sixVertex_cosh_antiferroelectricLambda hc]
  rw [Real.log_div hd.ne' (by norm_num : (2 : Real) ≠ 0)]
  ring

theorem continuousOn_sixVertexBetheDesingularizedLogObservable
    {c : Real} (hc : 2 < c) :
    ContinuousOn (sixVertexBetheDesingularizedLogObservable c)
      (Set.Icc 0 Real.pi) := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun x => a ^ 2 + 1 + 2 * a * Real.cos x
  let S : Real -> Real := fun x => Real.sinc (x / 2)
  have hAcont : Continuous A := by
    dsimp [A]
    fun_prop
  have hScont : Continuous S := by
    exact Real.continuous_sinc.comp (continuous_id.div_const 2)
  have hApos (x : Real) : 0 < A x := by
    have ha : 1 < a := by dsimp [a]; nlinarith
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hSpos (x : Real) (hx : x ∈ Set.Icc 0 Real.pi) : 0 < S x := by
    rcases hx.1.eq_or_lt with rfl | hx0
    · simp [S]
    · have hhalf0 : x / 2 ≠ 0 := by positivity
      dsimp [S]
      rw [Real.sinc_of_ne_zero hhalf0]
      exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
        (by nlinarith [hx.2, Real.pi_pos]))
        (by linarith)
  unfold sixVertexBetheDesingularizedLogObservable
  dsimp [a]
  apply ContinuousOn.sub
  · exact (continuous_const.mul (hAcont.log (fun x => (hApos x).ne'))).continuousOn
  · exact hScont.continuousOn.log (fun x hx => (hSpos x hx).ne')

theorem abs_sinc_sub_one_le_sq_div_four
    {x : Real} (hx : |x| <= 1) :
    |Real.sinc x - 1| <= x ^ 2 / 4 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  let u := |x|
  have hu0 : 0 < u := abs_pos.mpr hx0
  have hu1 : u <= 1 := hx
  have hsinc : Real.sinc x = Real.sin u / u := by
    rcases le_total 0 x with hxPos | hxNeg
    · have hux : u = x := by simp [u, abs_of_nonneg hxPos]
      rw [hux]
      exact Real.sinc_of_ne_zero hx0
    · have hux : u = -x := by simp [u, abs_of_nonpos hxNeg]
      calc
        Real.sinc x = Real.sinc (-x) := (Real.sinc_neg x).symm
        _ = Real.sin (-x) / (-x) :=
          Real.sinc_of_ne_zero (neg_ne_zero.mpr hx0)
        _ = Real.sin u / u := by rw [hux]
  have hsinUpper : Real.sin u <= u := Real.sin_le hu0.le
  have hsinLower : u - u ^ 3 / 4 <= Real.sin u :=
    (Real.sin_gt_sub_cube hu0 hu1).le
  have hsincUpper : Real.sin u / u <= 1 :=
    (div_le_one hu0).2 hsinUpper
  have hsincLower : 1 - u ^ 2 / 4 <= Real.sin u / u := by
    rw [le_div_iff₀ hu0]
    have : (1 - u ^ 2 / 4) * u = u - u ^ 3 / 4 := by ring
    rwa [this]
  rw [hsinc, abs_of_nonpos (sub_nonpos.mpr hsincUpper)]
  have huSq : u ^ 2 = x ^ 2 := sq_abs x
  rw [← huSq]
  linarith

theorem hasDerivAt_sinc_zero : HasDerivAt Real.sinc 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmajor : Tendsto (fun x : Real => |x| / 4) (nhdsWithin 0 {0}ᶜ)
      (nhds 0) := by
    have h := (continuous_abs.tendsto 0).div_const (4 : Real)
    simpa using h.mono_left inf_le_left
  apply squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _)) ?_ hmajor
  have hxne : ∀ᶠ x : Real in nhdsWithin 0 {0}ᶜ, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hsmallN : ∀ᶠ y : Real in nhds 0, |y| <= 1 :=
    Metric.eventually_nhds_iff.2 ⟨1, by norm_num, fun y hy => by
      simpa [Real.dist_eq] using le_of_lt hy⟩
  have hsmall : ∀ᶠ y : Real in nhdsWithin 0 {0}ᶜ, |y| <= 1 :=
    hsmallN.filter_mono inf_le_left
  filter_upwards [hxne, hsmall] with x hxne hxsmall
  have hbound := abs_sinc_sub_one_le_sq_div_four hxsmall
  unfold slope
  simp only [sub_zero, Real.sinc_zero, vsub_eq_sub, norm_smul,
    Real.norm_eq_abs, norm_inv]
  rw [inv_mul_eq_div]
  calc
    |Real.sinc x - 1| / |x| <= (x ^ 2 / 4) / |x| :=
      div_le_div_of_nonneg_right hbound (abs_nonneg x)
    _ = |x| / 4 := by
      rw [show x ^ 2 = |x| ^ 2 by simp [sq_abs]]
      field_simp [abs_pos.mpr hxne |>.ne']

end
end StatMech.FrontierD
