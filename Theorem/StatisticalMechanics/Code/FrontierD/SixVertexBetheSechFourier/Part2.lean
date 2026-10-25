/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part4
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSechFourier
open Filter MeasureTheory Set Topology
open scoped FourierTransform


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexSechProfile
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexSechProfile lam) := by
  unfold sixVertexSechProfile
  apply Complex.continuous_ofReal.comp
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact (Real.cosh_pos _).ne'

theorem fourier_sixVertexSechProfile
    {lam : Real} (hlam : 0 < lam) (n : Real) :
    𝓕 (sixVertexSechProfile lam) n =
      (1 / (2 * Real.cosh (n * lam)) : Real) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [sixVertexSechProfile, smul_eq_mul]
  rw [show (fun x : Real =>
      Complex.exp ((-2 * Real.pi * x * n : Real) * Complex.I) *
        (Real.pi / (2 * lam) /
          Real.cosh (Real.pi ^ 2 * x / lam) : Real)) =
      fun x => (Real.pi / (2 * lam) : Real) *
        (Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) /
          Real.cosh (Real.pi ^ 2 * x / lam)) by
    funext x
    push_cast
    ring]
  rw [MeasureTheory.integral_const_mul, integral_fourier_sech hlam]
  push_cast
  field_simp [hlam.ne', Real.pi_ne_zero, (Real.cosh_pos (n * lam)).ne']

theorem summable_one_div_two_cosh_nat
    {lam : Real} (hlam : 0 < lam) :
    Summable (fun n : Nat =>
      ((1 / (2 * Real.cosh ((n : Real) * lam)) : Real) : Complex)) := by
  let q := Real.exp (-lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun n : Nat => q ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  apply hgeom.of_norm_bounded
  intro n
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num)
      (Real.cosh_pos ((n : Real) * lam))))]
  have hsech : 1 / Real.cosh ((n : Real) * lam) ≤
      2 * Real.exp (-((n : Real) * lam)) := by
    have hcosh : Real.exp ((n : Real) * lam) ≤
        2 * Real.cosh ((n : Real) * lam) := by
      rw [Real.cosh_eq]
      nlinarith [Real.exp_pos (-((n : Real) * lam))]
    have hhalf : 1 / (2 * Real.cosh ((n : Real) * lam)) ≤
        1 / Real.exp ((n : Real) * lam) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hcosh
    calc
      1 / Real.cosh ((n : Real) * lam) =
          2 * (1 / (2 * Real.cosh ((n : Real) * lam))) := by
        field_simp [(Real.cosh_pos _).ne']
      _ ≤ 2 * (1 / Real.exp ((n : Real) * lam)) := by gcongr
      _ = 2 * Real.exp (-((n : Real) * lam)) := by
        rw [Real.exp_neg]
        ring
  have hbound :
      1 / (2 * Real.cosh ((n : Real) * lam)) ≤
        Real.exp (-((n : Real) * lam)) := by
    have hcoshNe := (Real.cosh_pos ((n : Real) * lam)).ne'
    rw [show 1 / (2 * Real.cosh ((n : Real) * lam)) =
      (1 / Real.cosh ((n : Real) * lam)) / 2 by
        field_simp [hcoshNe]]
    linarith
  calc
    1 / (2 * Real.cosh ((n : Real) * lam)) ≤
        Real.exp (-((n : Real) * lam)) := hbound
    _ = q ^ n := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem summable_fourier_sixVertexSechProfile_int
    {lam : Real} (hlam : 0 < lam) :
    Summable (fun n : Int =>
      FourierTransform.fourier (sixVertexSechProfile lam) (n : Real)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact (summable_one_div_two_cosh_nat hlam).congr fun n =>
      (fourier_sixVertexSechProfile hlam n).symm
  · exact (summable_one_div_two_cosh_nat hlam).congr fun n => by
      rw [fourier_sixVertexSechProfile hlam]
      have harg : ((-(n : Int) : Int) : Real) * lam =
          -((n : Real) * lam) := by
        push_cast
        ring
      rw [harg, Real.cosh_neg]

theorem one_div_cosh_le_two_mul_exp_neg
    {x : Real} (hx : 0 ≤ x) :
    1 / Real.cosh x ≤ 2 * Real.exp (-x) := by
  have hcosh : Real.exp x ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-x)]
  have hhalf : 1 / (2 * Real.cosh x) ≤ 1 / Real.exp x :=
    one_div_le_one_div_of_le (Real.exp_pos x) hcosh
  calc
    1 / Real.cosh x = 2 * (1 / (2 * Real.cosh x)) := by
      field_simp [(Real.cosh_pos x).ne']
    _ ≤ 2 * (1 / Real.exp x) := by gcongr
    _ = 2 * Real.exp (-x) := by rw [Real.exp_neg]; ring

theorem isBigO_one_div_cosh_mul_cocompact
    {a : Real} (ha : 0 < a) :
    (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
      =O[cocompact Real] fun x : Real => |x| ^ (-2 : Real) := by
  have htopExp :
      (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
        =O[Filter.atTop] fun x : Real => Real.exp (-a * x) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr (Real.cosh_pos (a * x)))]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    convert one_div_cosh_le_two_mul_exp_neg
      (mul_nonneg ha.le hx) using 1 <;> ring
  have htopPow :
      (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
        =O[Filter.atTop] fun x : Real => x ^ (-2 : Real) :=
    htopExp.trans (isLittleO_exp_neg_mul_rpow_atTop ha (-2)).isBigO
  have htop :
      (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
        =O[Filter.atTop] fun x : Real => |x| ^ (-2 : Real) := by
    apply htopPow.congr' EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [abs_of_nonneg hx]
  have hbot :
      (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex))
        =O[Filter.atBot] fun x : Real => |x| ^ (-2 : Real) := by
    have hcomp := htop.comp_tendsto tendsto_neg_atBot_atTop
    convert hcomp using 1 <;> funext x
    · simp only [Function.comp_apply]
      rw [mul_neg, Real.cosh_neg]
    · simp only [Function.comp_apply, abs_neg]
  rw [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup]
  exact ⟨hbot, htop⟩

theorem isBigO_sixVertexSechProfile_cocompact
    {lam : Real} (hlam : 0 < lam) :
    sixVertexSechProfile lam =O[cocompact Real]
      fun x : Real => |x| ^ (-2 : Real) := by
  let a : Real := Real.pi ^ 2 / lam
  have ha : 0 < a := div_pos (sq_pos_of_pos Real.pi_pos) hlam
  have hbase := isBigO_one_div_cosh_mul_cocompact ha
  have hscaled := hbase.const_mul_left
    ((Real.pi / (2 * lam) : Real) : Complex)
  apply hscaled.congr' _ EventuallyEq.rfl
  filter_upwards [] with x
  unfold sixVertexSechProfile
  dsimp [a]
  push_cast
  ring

theorem sixVertexSechProfile_poisson
    {lam : Real} (hlam : 0 < lam) (x : Real) :
    (∑' n : Int, sixVertexSechProfile lam (x + n)) =
      ∑' n : Int,
        ((1 / (2 * Real.cosh ((n : Real) * lam)) : Real) : Complex) *
          fourier n (x : UnitAddCircle) := by
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (continuous_sixVertexSechProfile hlam) one_lt_two
    (isBigO_sixVertexSechProfile_cocompact hlam)
    (summable_fourier_sixVertexSechProfile_int hlam) x
  simpa only [fourier_sixVertexSechProfile hlam] using h

end
end StatMech.FrontierD
