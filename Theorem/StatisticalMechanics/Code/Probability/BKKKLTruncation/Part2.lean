/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.LevelInfluenceBound.Part2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedRhoOptimise
import Def.StatisticalMechanics.Code.Probability.BKKKLTruncation
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bkt_master_of_residue {q : ℝ} (H : bkt_lowDegreeMasterResidue q) :
    pro_PBiasedMaster q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  set δ := maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hT
  set A := (4 * (ptn_sigma p) ^ 2 : ℝ) with hA
  
  rcases eq_or_lt_of_le hu0 with hu0' | hu0'
  · 
    rw [← hu0']
    exact bkt_master_endpoint_zero hp0 hp1 φ
  · rcases eq_or_lt_of_le hu1 with hu1' | hu1'
    · 
      rw [hu1']
      exact bkt_master_endpoint_one hp0 hp1 φ
    · 
      obtain ⟨k, hk⟩ := H p hp hp1 φ u hu0' hu1'
      have hsplit := bkt_trunc_split hp0 hp1 φ hu0' hu1' k
      
      
      have hAeq : (4 * p * (1 - p) : ℝ) = A := by rw [hA, ptn_sigma_sq hp0 hp1]; ring
      calc (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k),
                (S.card : ℝ) * (1 - u) ^ (S.card - 1)
                  * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
              + (1 - u) ^ k * (4 * p * (1 - p) * T) := hsplit
        _ ≤ A * (δ ^ (u / (2 - u)) - (1 - u) ^ k) * T
              + (1 - u) ^ k * (A * T) := by
            rw [hAeq]
            have := hk
            linarith [hk]
        _ = δ ^ (u / (2 - u)) * (A * T) := by ring


theorem bkt_budget_nonneg {u : ℝ} {δ : ℝ} (hu0 : 0 < u) (_hu1 : u < 1)
    (hδ0 : 0 < δ ^ (u / (2 - u))) :
    ∃ k : ℕ, 0 ≤ δ ^ (u / (2 - u)) - (1 - u) ^ k := by
  have h1u : (1 : ℝ) - u < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := δ ^ (u / (2 - u))) hδ0 h1u
  exact ⟨k, by linarith [hk]⟩


theorem bkt_residue_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) :
    ∃ k : ℕ,
      4 * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (0 : ℝ) ^ 2
        ≤ (4 * (ptn_sigma p) ^ 2)
          * ((maxInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
              ^ (u / (2 - u))
            - (1 - u) ^ k)
          * totalInfl (OSSS.bernoulliWeight p)
              (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) := by
  obtain ⟨k, hk⟩ := bkt_budget_nonneg hu0 hu1 hδ0
  refine ⟨k, ?_⟩
  
  have hlhs0 : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k),
      (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (0 : ℝ) ^ 2 = 0 := by
    rw [Finset.sum_eq_zero (fun S _ => by ring), mul_zero]
  rw [hlhs0]
  
  apply mul_nonneg
  · apply mul_nonneg (by positivity) hk
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _


theorem bkt_master_holds_degree1 [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hdeg : ∀ S : Finset ι, 2 ≤ S.card → ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S = 0)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * (4 * (ptn_sigma p) ^ 2
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  bkt_master_degree1 hp0 hp1 φ hdeg hu0 hu1


theorem bkt_degree1_witness (p : ℝ) :
    ∀ S : Finset ι, 2 ≤ S.card →
      ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) S = 0 := by
  intro S _
  have hf0 : (fun ω : ConfigSpace ι => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0)
      = (fun _ => (0 : ℝ)) := by funext ω; simp
  rw [hf0]
  unfold ptn_coeff
  rw [show (fun ω : ConfigSpace ι => (0 : ℝ) * ptn_pchar p S ω) = (fun _ => (0 : ℝ)) from by
    funext ω; ring]
  unfold OSSS.expect
  rw [Finset.sum_eq_zero (fun ω _ => by ring)]

end StatMech.Probability
