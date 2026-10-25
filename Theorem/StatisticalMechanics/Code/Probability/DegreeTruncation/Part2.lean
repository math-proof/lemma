/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.TwoPointHCqGt2.Part2
import Def.StatisticalMechanics.Code.Probability.DegreeTruncation
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem dtr_lowDegree_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    hcq_lowRangeResidue q := by
  intro p hp hp1 E _ _ _ φ hδ u hu0 hu1 hlow
  have hp0 : 0 < p := by have := hp.1; linarith
  
  have hlow' : u < 1 - 4 * p * (1 - p) ∨
      (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u) - (2 / dtr_qstar p u - 1))
        < 4 * (ptn_sigma p) ^ 2 := by
    rcases hlow with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [dtr_qstar]; exact h)
  obtain ⟨k, hk⟩ := H p hp hp1 φ hδ u hu0 hu1 hlow'
  
  have hsplit := dtr_trunc_split hp0 hp1 φ hu0 hu1 k
  set T := totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hT
  set δ := maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hδdef
  calc (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          + (1 - u) ^ k * (4 * p * (1 - p) * T) := hsplit
    _ ≤ (δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k) * T
          + (1 - u) ^ k * (4 * p * (1 - p) * T) := by linarith [hk]
    _ = δ ^ (u / (2 - u)) * T := by ring


theorem dtr_smallDelta_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    cvg_smallDeltaResidue q :=
  hcq_smallDelta_of_lowRange (dtr_lowDegree_of_residue H)


theorem dtr_martingaleHC_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    mxd_martingaleHC_statement q :=
  cvg_martingaleHC_of_smallDelta (dtr_smallDelta_of_residue H)


theorem dtr_budget_pos {p δ u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (_hu1 : u < 1)
    (hδ0 : 0 < δ ^ (u / (2 - u))) :
    ∃ k : ℕ, 0 ≤ δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k := by
  have hs0 : 0 < 4 * p * (1 - p) := by nlinarith
  have h1u : (1 : ℝ) - u < 1 := by linarith
  
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := δ ^ (u / (2 - u)) / (4 * p * (1 - p)))
    (by positivity) h1u
  refine ⟨k, ?_⟩
  rw [lt_div_iff₀ hs0] at hk
  nlinarith [hk]


theorem dtr_residue_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ k : ℕ, (0 : ℝ)
      ≤ ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          - 4 * p * (1 - p) * (1 - u) ^ k)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  obtain ⟨k, hk⟩ := dtr_budget_pos hp0 hp1 hu0 hu1 hδ0
  refine ⟨k, ?_⟩
  apply mul_nonneg hk
  exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _


theorem dtr_high_part_proved {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (1 - u) ^ k * (4 * p * (1 - p)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  dtr_high_part_le hp0 hp1 φ hu0 hu1 k

end StatMech.Probability
