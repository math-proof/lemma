/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.FSMartingale.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.MaxElementDecomp.Part4
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]


theorem mxd_dampFiber_nonneg [Nonempty ι] (p ρ : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) :
    0 ≤ mxd_dampFiber p ρ φ e := by
  unfold mxd_dampFiber
  exact Finset.sum_nonneg (fun S _ => by positivity)


theorem mxd_dampFiber_eq_fiber_perCoord [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) :
    mxd_dampFiber p ρ φ e
      = ρ ^ 2 * (ptn_sigma p) ^ 2 * ∑ S ∈ mxd_fiber e,
          (ρ ^ (S.erase e).card) ^ 2
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2 := by
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  unfold mxd_dampFiber
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have heS : e ∈ S := mxd_mem_of_mem_fiber hS
  have hcard : S.card = (S.erase e).card + 1 := by
    rw [Finset.card_erase_of_mem heS]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, heS⟩
    omega
  rw [hcard, div_pow, pow_succ]
  field_simp
  ring


theorem mxd_dampFiber_le_perCoord [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) (φ : ConfigSpace ι → Bool) (e : ι) :
    mxd_dampFiber p ρ φ e
      ≤ ρ ^ 2 * (ptn_sigma p) ^ 2
        * (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  rw [mxd_dampFiber_eq_fiber_perCoord hp0 hp1 ρ φ e]
  have hcoef : 0 ≤ ρ ^ 2 * (ptn_sigma p) ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoef
  
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mxd_fiber_subset_mem e)
    (fun S _ _ => by positivity)) ?_
  exact ptn_perCoord_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ e


theorem mxd_dampFiber_sum_eq [Nonempty ι] (p ρ : ℝ) (φ : ConfigSpace ι → Bool) :
    (∑ e : ι, mxd_dampFiber p ρ φ e)
      = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  unfold mxd_dampFiber mxd_fiber
  rw [Finset.sum_fiberwise (univ.erase (∅ : Finset ι)) mxd_maxE
      (fun S => (ρ ^ S.card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)]


theorem mxd_dampFiber_sum_cap [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) (φ : ConfigSpace ι → Bool) :
    (∑ e : ι, mxd_dampFiber p ρ φ e)
      ≤ ρ ^ 2 * (ptn_sigma p) ^ 2
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  have hcoef : 0 ≤ ρ ^ 2 * (ptn_sigma p) ^ 2 := by positivity
  calc (∑ e : ι, mxd_dampFiber p ρ φ e)
      ≤ ∑ e : ι, ρ ^ 2 * (ptn_sigma p) ^ 2
          * (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) :=
        Finset.sum_le_sum (fun e _ => mxd_dampFiber_le_perCoord hp0 hp1 h0 h1 hq1 hq2 hρsq φ e)
    _ = ρ ^ 2 * (ptn_sigma p) ^ 2
          * ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
        rw [Finset.mul_sum]
    _ ≤ ρ ^ 2 * (ptn_sigma p) ^ 2
          * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
        mul_le_mul_of_nonneg_left (ptn_cap_sum hp0 hp1 hq1 hq2 φ) hcoef


theorem mxd_dampFiber_pos [Nonempty ι] {p ρ : ℝ} (hρ : 0 < ρ)
    (φ : ConfigSpace ι → Bool) (e : ι)
    (hae : 0 < mxd_fiberWeight p φ e) :
    0 < mxd_dampFiber p ρ φ e := by
  unfold mxd_fiberWeight at hae
  unfold mxd_dampFiber
  
  have hwit : ∃ S ∈ mxd_fiber e,
      0 < (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
    by_contra h
    have hall : ∀ S ∈ mxd_fiber e,
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 = 0 := by
      intro S hS
      exact le_antisymm (not_lt.mp (fun hlt => h ⟨S, hS, hlt⟩)) (by positivity)
    rw [Finset.sum_eq_zero hall] at hae
    exact (lt_irrefl 0) hae
  obtain ⟨S, hS, hSpos⟩ := hwit
  apply Finset.sum_pos'
  · intro S' _; positivity
  · exact ⟨S, hS, by have : 0 < (ρ ^ S.card) ^ 2 := by positivity
                     exact mul_pos this hSpos⟩


theorem mxd_logSum_var [Nonempty ι] {p ρ : ℝ} (hρ : 0 < ρ) (φ : ConfigSpace ι → Bool)
    (hpos : 0 < ∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e),
      mxd_fiberWeight p φ e) :
    (∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e)
        * Real.log ((∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e)
          / (∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_dampFiber p ρ φ e))
      ≤ ∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e),
        mxd_fiberWeight p φ e * Real.log (mxd_fiberWeight p φ e / mxd_dampFiber p ρ φ e) := by
  apply esd_logSum (univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e))
    (fun e => mxd_fiberWeight p φ e) (fun e => mxd_dampFiber p ρ φ e)
  · intro e _; exact mxd_fiberWeight_nonneg p φ e
  · intro e he
    rw [Finset.mem_filter] at he
    exact mxd_dampFiber_pos hρ φ e he.2
  · exact hpos


theorem mxd_supp_var [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    (∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e), mxd_fiberWeight p φ e)
      = OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  rw [mxd_var_decomp hp0 hp1]
  rw [← Finset.sum_filter_add_sum_filter_not univ
    (fun e : ι => 0 < mxd_fiberWeight p φ e) (fun e => mxd_fiberWeight p φ e)]
  have hzero : (∑ e ∈ univ.filter (fun e : ι => ¬ 0 < mxd_fiberWeight p φ e),
      mxd_fiberWeight p φ e) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [Finset.mem_filter] at he
    have hnn := mxd_fiberWeight_nonneg p φ e
    linarith [he.2]
  rw [hzero, add_zero]


theorem mxd_logSum_gain [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hρ : 0 < ρ) (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) (φ : ConfigSpace ι → Bool)
    (hVpos : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hTpos : 0 < totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
    OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          / (ρ ^ 2 * (ptn_sigma p) ^ 2
            * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
              * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))))
      ≤ ∑ e ∈ univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e),
        mxd_fiberWeight p φ e * Real.log (mxd_fiberWeight p φ e / mxd_dampFiber p ρ φ e) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set V := OSSS.var (OSSS.bernoulliWeight p) f with hVd
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδd
  set T := totalInfl (OSSS.bernoulliWeight p) f with hTd
  set t := univ.filter (fun e : ι => 0 < mxd_fiberWeight p φ e) with htdef
  set Vt := ∑ e ∈ t, mxd_fiberWeight p φ e with hVtd
  set D := ∑ e ∈ t, mxd_dampFiber p ρ φ e with hDd
  set K := ρ ^ 2 * (ptn_sigma p) ^ 2 * (δ ^ (2 / q - 1) * T) with hKd
  
  have hVtV : Vt = V := mxd_supp_var hp0 hp1 φ
  have hVtpos : 0 < Vt := by rw [hVtV]; exact hVpos
  
  have hDpos : 0 < D := by
    rw [hDd]
    obtain ⟨e, he⟩ : ∃ e, e ∈ t := by
      by_contra h
      have : Vt = 0 := Finset.sum_eq_zero (fun e he => absurd he (fun hh => h ⟨e, hh⟩))
      linarith [hVtpos, this]
    rw [htdef, Finset.mem_filter] at he
    apply Finset.sum_pos'
    · intro e' _; exact mxd_dampFiber_nonneg p ρ φ e'
    · exact ⟨e, by rw [htdef, Finset.mem_filter]; exact ⟨Finset.mem_univ e, he.2⟩,
        mxd_dampFiber_pos hρ φ e he.2⟩
  
  have hDcap : D ≤ K := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun e _ _ => mxd_dampFiber_nonneg p ρ φ e)) ?_
    rw [hKd]
    exact mxd_dampFiber_sum_cap hp0 hp1 hρ.le h1 hq1 hq2 hρsq φ
  have hKpos : 0 < K := by
    rw [hKd]
    have hσ2 : 0 < (ptn_sigma p) ^ 2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
    have hδpow : 0 < δ ^ (2 / q - 1) := Real.rpow_pos_of_pos hδ0 _
    positivity
  
  have hgain := mxd_logSum_var hρ φ (by rw [← hVtd]; exact hVtpos)
  
  have hmono : Real.log (V / K) ≤ Real.log (Vt / D) := by
    rw [hVtV]
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left hVpos.le hDpos hDcap
  calc V * Real.log (V / K)
      = Vt * Real.log (V / K) := by rw [hVtV]
    _ ≤ Vt * Real.log (Vt / D) := by
        apply mul_le_mul_of_nonneg_left hmono hVtpos.le
    _ ≤ ∑ e ∈ t, mxd_fiberWeight p φ e * Real.log (mxd_fiberWeight p φ e / mxd_dampFiber p ρ φ e) :=
        hgain


end StatMech.Probability
