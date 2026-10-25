/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.FSMartingale.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.MaxElementDecomp.Part5
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]


theorem mxd_rhoOptimise_of_martingaleHC {q : ℝ} (H : mxd_martingaleHC_statement q) :
    ptn_RhoOptimise q := by
  intro p hp hp1 E _ _ _ φ _Hcap
  have hp0 : 0 < p := by have := hp.1; linarith
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set cf := fun S : Finset E => (ptn_coeff p f S) ^ 2 with hcf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set V := ∑ S ∈ (univ.erase (∅ : Finset E)), cf S with hV
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  
  have hVvar : V = OSSS.var (OSSS.bernoulliWeight p) f := (ptn_var_eq_fourierWeight hp0 hp1 f).symm
  
  have Hfam : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S)
        ≤ δ ^ (u / (2 - u)) * T := by
    intro u hu0 hu1
    have := H p hp hp1 φ u hu0 hu1
    rw [hcf, hδ, hT]; exact this
  have hVnn : 0 ≤ V := by rw [hV]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hTnn : 0 ≤ T := by rw [hT]; exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hδnn : 0 ≤ δ := by
    rw [hδ]; exact kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  
  rw [← hVvar]
  show 2 * V * Real.log (1 / δ) ≤ T
  rcases lt_trichotomy δ 1 with hδ1 | hδ1 | hδ1
  · rcases eq_or_lt_of_le hδnn with hδ0 | hδ0
    · rw [← hδ0, div_zero, Real.log_zero, mul_zero]; exact hTnn
    · 
      have ht : 0 < -(Real.log δ) := by have := Real.log_neg hδ0 hδ1; linarith
      have hlogeq : Real.log (1 / δ) = -(Real.log δ) := by
        rw [Real.log_div one_ne_zero (ne_of_gt hδ0), Real.log_one, zero_sub]
      have hIntLhs : (∫ u in (0:ℝ)..1, ∑ S : Finset E, 4 * (S.card : ℝ)
          * (1 - u) ^ (S.card - 1) * cf S) = 4 * V := cro2_integral_lhs cf
      have hIntRhs : (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u)) * T) ≤ T * (2 / (-(Real.log δ))) := by
        rw [intervalIntegral.integral_mul_const, mul_comm T _]
        exact mul_le_mul_of_nonneg_right (cro2_integral_rhs_le δ hδ0 hδ1) hTnn
      have hmono : (∫ u in (0:ℝ)..1, ∑ S : Finset E, 4 * (S.card : ℝ)
            * (1 - u) ^ (S.card - 1) * cf S)
          ≤ (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u)) * T) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · apply Continuous.intervalIntegrable; fun_prop
        · exact (cro2_rpow_integrable δ hδ0).mul_const T
        · intro u hu
          simp only [Set.mem_Icc] at hu
          exact Hfam u hu.1 hu.2
      rw [hIntLhs] at hmono
      have hfin : 4 * V ≤ T * (2 / (-(Real.log δ))) := le_trans hmono hIntRhs
      rw [hlogeq]
      rw [mul_div_assoc'] at hfin
      rw [le_div_iff₀ ht] at hfin
      nlinarith [hfin, ht]
  · rw [hδ1, div_one, Real.log_one, mul_zero]; exact hTnn
  · have hlog : Real.log (1 / δ) ≤ 0 := by
      rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub, neg_nonpos]
      exact Real.log_nonneg (by linarith)
    nlinarith [hVnn, hTnn, hlog]


theorem mxd_decomp_and_gain [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hρ : 0 < ρ) (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) (φ : ConfigSpace ι → Bool)
    (hVpos : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hTpos : 0 < totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
    OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        = ∑ e : ι, mxd_fiberWeight p φ e
      ∧ OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * Real.log (OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            / (ρ ^ 2 * (ptn_sigma p) ^ 2
              * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))))
        ≤ ∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e),
          mxd_fiberWeight p φ e * Real.log (mxd_fiberWeight p φ e / mxd_dampFiber p ρ φ e) :=
  ⟨mxd_var_decomp hp0 hp1 φ,
   mxd_logSum_gain hp0 hp1 hρ h1 hq1 hq2 hρsq φ hVpos hδ0 hTpos⟩


theorem mxd_martingaleHC_c0 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (u : ℝ) :
    (∑ S : Finset E, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hzero : (∑ S : Finset E, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
      * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 0 := by
    apply Finset.sum_eq_zero; intro S _; ring
  rw [hzero]
  have hδnn : 0 ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
    kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _
  have hTnn : 0 ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
    kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _
  positivity

end StatMech.Probability
