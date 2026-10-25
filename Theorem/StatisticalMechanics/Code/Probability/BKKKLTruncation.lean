/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.LevelInfluenceBound.Part2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedRhoOptimise
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bkt_high_part_decay {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (1 - u) ^ k * (4 * p * (1 - p)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  dtr_high_part_le hp0 hp1 φ hu0 hu1 k


theorem bkt_trunc_split {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        + (1 - u) ^ k * (4 * p * (1 - p)
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  dtr_trunc_split hp0 hp1 φ hu0 hu1 k


theorem bkt_lhs_eq_level1_of_degree1 {p : ℝ} (φ : ConfigSpace ι → Bool) (u : ℝ)
    (hdeg : ∀ S : Finset ι, 2 ≤ S.card → ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S = 0) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
          (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  
  have hRHS : 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), c S
      = ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
          4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [hS.2, Nat.cast_one, show (1 : ℕ) - 1 = 0 from rfl, pow_zero]; ring
  rw [hRHS]
  
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun S : Finset ι => S.card = 1)
      (fun S => 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)]
  have hcompl : (∑ S ∈ univ.filter (fun S : Finset ι => ¬ S.card = 1),
        4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    have hne : S.card ≠ 1 := hS.2
    rcases Nat.lt_or_ge S.card 2 with hlt | hge
    · 
      have hc0 : S.card = 0 := by omega
      rw [hc0]; simp
    · 
      have hcS0 : c S = 0 := by simp only [hc]; rw [hdeg S hge]; ring
      rw [hcS0]; ring
  rw [hcompl, add_zero]


theorem bkt_level1_endpoint_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * p * (1 - p)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set c := fun S : Finset ι => (ptn_coeff p f S) ^ 2 with hc
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ2pos : (0:ℝ) < (ptn_sigma p) ^ 2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  
  have hfull : (∑ S : Finset ι, 4 * (S.card : ℝ) * c S)
      = 4 * p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) f := by
    have hppos : (0:ℝ) < p * (1 - p) := by nlinarith
    have heq : totalInfl (OSSS.bernoulliWeight p) f
        = (1 / (p * (1 - p))) * ∑ S : Finset ι, (S.card : ℝ) * c S := by
      rw [ptn_totalInfl_eq_fourierWeight hp0 hp1, hσ2]
    rw [heq]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro S _
    rw [show 4 * p * (1 - p) * (1 / (p * (1 - p)) * ((S.card : ℝ) * c S))
        = (4 * ((p * (1 - p)) / (p * (1 - p)))) * ((S.card : ℝ) * c S) from by ring]
    rw [div_self (ne_of_gt hppos)]; ring
  rw [← hfull]
  
  rw [Finset.mul_sum]
  calc (∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), 4 * c S)
      = ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), 4 * (S.card : ℝ) * c S := by
        apply Finset.sum_congr rfl; intro S hS
        rw [Finset.mem_filter] at hS; rw [hS.2]; push_cast; ring
    _ ≤ ∑ S : Finset ι, 4 * (S.card : ℝ) * c S := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S _ _; rw [hc]; positivity


theorem bkt_level1_endpoint_one [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * p * (1 - p)
        * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set σ2 := (ptn_sigma p) ^ 2 with hσ2def
  have hσ2 : σ2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ2pos : 0 < σ2 := by rw [hσ2]; nlinarith
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := ι) hp0.le hp1.le
  
  have hρ0 : (0:ℝ) ≤ (0:ℝ) := le_refl _
  have hρ1 : (0:ℝ) ≤ 1 := by norm_num
  have hq1 : (1 : ℝ) ≤ 1 := le_refl _
  have hq2 : (1 : ℝ) ≤ 2 := by norm_num
  have hρsq : (0:ℝ) ^ 2 = (1 - 1) * 4 * p * (1 - p) := by ring
  have hθ1 : (1 : ℝ) ≤ 2 / 1 := by norm_num
  
  have hper : ∀ e : ι,
      (ptn_coeff p f {e}) ^ 2 ≤ σ2 * (δ * OSSS.infl (OSSS.bernoulliWeight p) f e) := by
    intro e
    have hpc := ptn_perCoord_hc hp0 hp1 hρ0 hρ1 hq1 hq2 hρsq φ e
    have hmem : ({e} : Finset ι) ∈ univ.filter (fun S : Finset ι => e ∈ S) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Finset.mem_singleton_self e⟩
    have hsingle_term : ((0:ℝ) ^ (({e} : Finset ι).erase e).card) ^ 2 * (ptn_coeff p f {e} / ptn_sigma p) ^ 2
        = (ptn_coeff p f {e} / ptn_sigma p) ^ 2 := by
      rw [Finset.erase_singleton, Finset.card_empty, pow_zero, one_pow, one_mul]
    have hge : (ptn_coeff p f {e} / ptn_sigma p) ^ 2
        ≤ ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
            ((0:ℝ) ^ (S.erase e).card) ^ 2 * (ptn_coeff p f S / ptn_sigma p) ^ 2 := by
      rw [← hsingle_term]
      apply Finset.single_le_sum (f := fun S => ((0:ℝ) ^ (S.erase e).card) ^ 2 * (ptn_coeff p f S / ptn_sigma p) ^ 2)
        (fun S _ => by positivity) hmem
    have hIe : (ptn_coeff p f {e} / ptn_sigma p) ^ 2 ≤ (OSSS.infl (OSSS.bernoulliWeight p) f e) ^ ((2:ℝ) / 1) :=
      le_trans hge hpc
    have hcap : (OSSS.infl (OSSS.bernoulliWeight p) f e) ^ ((2:ℝ) / 1)
        ≤ δ ^ ((2:ℝ) / 1 - 1) * OSSS.infl (OSSS.bernoulliWeight p) f e :=
      bph_cap_term _ _ _ (kkl_infl_nonneg hprob f e) (kkl_infl_le_maxInfl _ f e) hθ1
    rw [show (2:ℝ) / 1 - 1 = 1 by norm_num, Real.rpow_one] at hcap
    have hσne : (ptn_sigma p) ^ 2 ≠ 0 := by rw [← hσ2def]; exact ne_of_gt hσ2pos
    have hcoeff : σ2 * (ptn_coeff p f {e} / ptn_sigma p) ^ 2 = (ptn_coeff p f {e}) ^ 2 := by
      rw [div_pow, hσ2def, mul_div_assoc', mul_comm, mul_div_assoc, div_self hσne, mul_one]
    rw [← hcoeff]
    apply mul_le_mul_of_nonneg_left (le_trans hIe hcap) hσ2pos.le
  
  have hreindex : (∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p f S) ^ 2)
      = ∑ e : ι, (ptn_coeff p f {e}) ^ 2 := by
    have hset : univ.filter (fun S : Finset ι => S.card = 1)
        = (Finset.univ : Finset ι).map ⟨fun e => ({e} : Finset ι), fun a b h => by simpa using h⟩ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hS; obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hS; exact ⟨a, ha.symm⟩
      · rintro ⟨e, rfl⟩; exact Finset.card_singleton e
    rw [hset, Finset.sum_map]; rfl
  rw [hreindex]
  calc (4 : ℝ) * ∑ e : ι, (ptn_coeff p f {e}) ^ 2
      ≤ 4 * ∑ e : ι, σ2 * (δ * OSSS.infl (OSSS.bernoulliWeight p) f e) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum (fun e _ => hper e)
    _ = 4 * σ2 * δ * (∑ e : ι, OSSS.infl (OSSS.bernoulliWeight p) f e) := by
        rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring
    _ = 4 * p * (1 - p) * δ * totalInfl (OSSS.bernoulliWeight p) f := by
        rw [hσ2, totalInfl]; ring


theorem bkt_master_degree1 [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hdeg : ∀ S : Finset ι, 2 ≤ S.card → ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S = 0)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * (4 * (ptn_sigma p) ^ 2
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  rw [bkt_lhs_eq_level1_of_degree1 φ u hdeg]
  
  rw [show δ ^ (u / (2 - u)) * (4 * (ptn_sigma p) ^ 2 * T)
      = 4 * p * (1 - p) * δ ^ (u / (2 - u)) * T from by rw [hσ2]; ring]
  
  rcases eq_or_lt_of_le hu1 with hu1' | hu1'
  · 
    subst hu1'
    rw [show (1:ℝ) / (2 - 1) = 1 by norm_num, Real.rpow_one]
    exact bkt_level1_endpoint_one hp0 hp1 φ
  · 
    rcases eq_or_lt_of_le hu0 with hu0' | hu0'
    · 
      subst hu0'
      rw [show (0:ℝ) / (2 - 0) = 0 by norm_num, Real.rpow_zero, mul_one]
      exact bkt_level1_endpoint_zero hp0 hp1 φ
    · 
      exact lib_level1_mass_le hp0 hp1 φ hu0' hu1'


theorem bkt_master_endpoint_zero [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (0:ℝ)) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((0:ℝ) / (2 - 0))
        * (4 * (ptn_sigma p) ^ 2
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set c := fun S : Finset ι => (ptn_coeff p f S) ^ 2 with hc
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hppos : (0:ℝ) < p * (1 - p) := by nlinarith
  rw [show (0:ℝ) / (2 - 0) = 0 by norm_num, Real.rpow_zero, one_mul]
  
  have hLHS : (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (0:ℝ)) ^ (S.card - 1) * c S)
      = ∑ S : Finset ι, 4 * (S.card : ℝ) * c S := by
    apply Finset.sum_congr rfl; intro S _
    rw [show (1:ℝ) - 0 = 1 by norm_num, one_pow, mul_one]
  rw [hLHS]
  rw [show 4 * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) f
      = 4 * p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) f from by rw [hσ2]; ring]
  apply le_of_eq
  have heq : totalInfl (OSSS.bernoulliWeight p) f
      = (1 / (p * (1 - p))) * ∑ S : Finset ι, (S.card : ℝ) * c S := by
    rw [ptn_totalInfl_eq_fourierWeight hp0 hp1, hσ2]
  rw [heq, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro S _
  rw [show 4 * p * (1 - p) * (1 / (p * (1 - p)) * ((S.card : ℝ) * c S))
      = (4 * ((p * (1 - p)) / (p * (1 - p)))) * ((S.card : ℝ) * c S) from by ring]
  rw [div_self (ne_of_gt hppos)]; ring


theorem bkt_master_endpoint_one [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (1:ℝ)) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((1:ℝ) / (2 - 1))
        * (4 * (ptn_sigma p) ^ 2
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  set c := fun S : Finset ι => (ptn_coeff p f S) ^ 2 with hc
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  
  have hLHS : (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (1:ℝ)) ^ (S.card - 1) * c S)
      = 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), c S := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun S : Finset ι => S.card = 1)
        (fun S => 4 * (S.card : ℝ) * (1 - (1:ℝ)) ^ (S.card - 1) * c S)]
    have hcompl : (∑ S ∈ univ.filter (fun S : Finset ι => ¬ S.card = 1),
          4 * (S.card : ℝ) * (1 - (1:ℝ)) ^ (S.card - 1) * c S) = 0 := by
      apply Finset.sum_eq_zero; intro S hS
      rw [Finset.mem_filter] at hS
      rcases Nat.lt_or_ge S.card 2 with hlt | hge
      · have hc0 : S.card = 0 := by omega
        rw [hc0]; simp
      · 
        have hge1 : 1 ≤ S.card - 1 := by omega
        rw [show (1:ℝ) - 1 = 0 by norm_num, zero_pow (by omega : S.card - 1 ≠ 0)]; ring
    rw [hcompl, add_zero]
    apply Finset.sum_congr rfl; intro S hS
    rw [Finset.mem_filter] at hS
    rw [hS.2, Nat.cast_one, show (1 : ℕ) - 1 = 0 from rfl, pow_zero]; ring
  rw [hLHS]
  rw [show (1:ℝ) / (2 - 1) = 1 by norm_num, Real.rpow_one]
  rw [show δ * (4 * (ptn_sigma p) ^ 2 * T) = 4 * p * (1 - p) * δ * T from by rw [hσ2]; ring]
  exact bkt_level1_endpoint_one hp0 hp1 φ


end StatMech.Probability
