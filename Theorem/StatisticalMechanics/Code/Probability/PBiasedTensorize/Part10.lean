/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part10
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_qnormPow_deriv {p q : ℝ} (hq : 0 < q) (φ : ConfigSpace ι → Bool) (e : ι) :
    ptn_qnormPow p q (ptn_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e)
      = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
  unfold ptn_qnormPow OSSS.infl ptn_deriv
  congr 1; funext ω
  simp only
  by_cases hO : φ (StatMech.setOpen e ω) <;> by_cases hC : φ (StatMech.setClosed e ω) <;>
    simp [hO, hC, Real.one_rpow, Real.zero_rpow (ne_of_gt hq)]


theorem ptn_qnorm_deriv_sq {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ConfigSpace ι → Bool) (e : ι) :
    (ptn_qnorm p q (ptn_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e)) ^ 2
      = (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  unfold ptn_qnorm
  rw [ptn_qnormPow_deriv hq φ e]
  set Ie := OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e with hIe
  have hIenn : 0 ≤ Ie := by
    rw [hIe]; exact OSSS.infl_nonneg (bernoulliWeight_isProbWeight hp0.le hp1.le) _ e
  rw [show (Ie ^ (1 / q)) ^ 2 = (Ie ^ (1 / q)) ^ (2:ℝ) from by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
  rw [← Real.rpow_mul hIenn]
  congr 1; field_simp


theorem ptn_kop_deriv_l2sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (f : ConfigSpace ι → ℝ)
    (e : ι) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun x => (ptn_kop p ρ (ptn_deriv f e) x) ^ 2)
      = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p f S / ptn_sigma p) ^ 2 := by
  
  have heq : ptn_deriv f e
      = fun x => ∑ S ∈ univ.filter (fun S => e ∈ S),
          (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) x := by
    funext ω; exact ptn_deriv_fourier hp0 hp1 f e ω
  
  rw [heq]
  have hkop : ptn_kop p ρ (fun x => ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ptn_coeff p f S / ptn_sigma p) * ptn_pchar p (S.erase e) x)
      = fun x => ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        ((ptn_coeff p f S / ptn_sigma p) * ρ ^ (S.erase e).card) * ptn_pchar p (S.erase e) x := by
    rw [ptn_kop_finsetSum]
    funext x
    apply Finset.sum_congr rfl
    intro S _
    rw [ptn_kop_const_mul p ρ (ptn_coeff p f S / ptn_sigma p) (ptn_pchar p (S.erase e))]
    change (ptn_coeff p f S / ptn_sigma p) * ptn_kop p ρ (ptn_pchar p (S.erase e)) x = _
    rw [ptn_kop_pchar_apply hp0 hp1]; ring
  rw [hkop]
  rw [ptn_expect_sum_pchar_sq hp0 hp1 _ (fun S => (ptn_coeff p f S / ptn_sigma p) * ρ ^ (S.erase e).card)
      (fun S => S.erase e) (ptn_erase_injOn e)]
  apply Finset.sum_congr rfl
  intro S _; ring


theorem ptn_perCoord_hc {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (φ : ConfigSpace ι → Bool) (e : ι) :
    (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
          / ptn_sigma p) ^ 2)
      ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  have hldw := ptn_lowDegreeWeight hp0 hp1 h0 h1 hq1 hq2 hρsq (ptn_deriv f e)
  
  rw [show (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p (ptn_deriv f e) S) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun x => (ptn_kop p ρ (ptn_deriv f e) x) ^ 2) from by
        rw [ptn_kop_eq_noiseOp hp0 hp1, ptn_noiseOp_l2sq hp0 hp1]] at hldw
  rw [ptn_kop_deriv_l2sq hp0 hp1] at hldw
  rw [ptn_qnorm_deriv_sq hp0 hp1 (by linarith : (0:ℝ) < q)] at hldw
  exact hldw


theorem ptn_summed_hc {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (φ : ConfigSpace ι → Bool) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  set σ2 := (ptn_sigma p) ^ 2 with hσ2
  set cc := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hcc
  have hσ2pos : 0 < σ2 := by rw [hσ2]; exact pow_pos (ptn_sigma_pos hp0 hp1) 2
  
  have hper : ∀ e : ι,
      (1 / σ2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * cc S
        ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
    intro e
    have h := ptn_perCoord_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ e
    refine le_trans (le_of_eq ?_) h
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hcc, div_pow, one_div, hσ2]; ring
  refine le_trans ?_ (Finset.sum_le_sum (fun e _ => hper e))
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  
  apply le_of_eq
  symm
  have hinner : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * cc S)
      = ∑ S : Finset ι, (if e ∈ S then (ρ ^ (S.card - 1)) ^ 2 * cc S else 0) := by
    intro e
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases he : e ∈ S
    · rw [if_pos he, if_pos he, Finset.card_erase_of_mem he]
    · rw [if_neg he, if_neg he]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]


theorem ptn_cap_sum [Nonempty ι] {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (φ : ConfigSpace ι → Bool) :
    (∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p)
        (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q))
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set θ := 2 / q with hθdef
  have hθ1 : 1 ≤ θ := by rw [hθdef, le_div_iff₀ (by linarith)]; linarith
  have hprob := bernoulliWeight_isProbWeight (E := ι) hp0.le hp1.le
  have hterm : ∀ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) f e) ^ θ
      ≤ δ ^ (θ - 1) * (OSSS.infl (OSSS.bernoulliWeight p) f e) :=
    fun e => bph_cap_term _ _ _ (kkl_infl_nonneg hprob f e) (kkl_infl_le_maxInfl _ f e) hθ1
  calc (∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) f e) ^ θ)
      ≤ ∑ e : ι, δ ^ (θ - 1) * (OSSS.infl (OSSS.bernoulliWeight p) f e) :=
        Finset.sum_le_sum (fun e _ => hterm e)
    _ = δ ^ (θ - 1) * totalInfl (OSSS.bernoulliWeight p) f := by
        rw [← Finset.mul_sum]
        rfl


theorem ptn_capped_hc [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (φ : ConfigSpace ι → Bool) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  le_trans (ptn_summed_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ) (ptn_cap_sum hp0 hp1 hq1 hq2 φ)


end StatMech.Probability
