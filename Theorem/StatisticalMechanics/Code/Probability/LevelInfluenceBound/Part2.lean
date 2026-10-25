/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/LevelInfluenceBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.DegreeTruncation.Part2
import Def.StatisticalMechanics.Code.Probability.LevelInfluenceBound
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem lib_levelGe2_discharges {q : ℝ} (H : lib_levelGe2Residue q) :
    dtr_lowDegreeResidue q := by
  intro p hp hp1 E _ _ _ φ hδ u hu0 hu1 hlow
  have hp0 : 0 < p := by have := hp.1; linarith
  
  obtain ⟨k, hk1, hk⟩ := H p hp hp1 φ hδ u hu0 hu1 hlow
  set f := fun ω : ConfigSpace E => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδdef
  set T := totalInfl (OSSS.bernoulliWeight p) f with hTdef
  
  have hlvl1 : 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1), (ptn_coeff p f S) ^ 2
      ≤ 4 * p * (1 - p) * δ ^ (u / (2 - u)) * T := lib_level1_mass_le hp0 hp1 φ hu0 hu1
  
  set B : ℝ := (δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k) * T with hB
  
  have hrhs : ((δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k
        - 4 * p * (1 - p) * δ ^ (u / (2 - u))) * T)
      = B - 4 * p * (1 - p) * δ ^ (u / (2 - u)) * T := by rw [hB]; ring
  rw [hrhs] at hk
  
  have hk' : 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
      (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p f S) ^ 2
      ≤ B - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1), (ptn_coeff p f S) ^ 2 := by
    refine le_trans hk ?_
    linarith [hlvl1]
  
  have hfinal := (lib_residue_iff_levelGe2 φ hk1 (B := B)).mpr hk'
  exact ⟨k, hfinal⟩


theorem lib_levelGe2_budget_pos {p δ u : ℝ} (hphalf : 1 / 2 < p) (hp1 : p < 1) (hu0 : 0 < u)
    (_hu1 : u < 1) (hδ0 : 0 < δ ^ (u / (2 - u))) :
    ∃ k : ℕ, 1 ≤ k ∧ 0 ≤ δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k
        - 4 * p * (1 - p) * δ ^ (u / (2 - u)) := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < 4 * p * (1 - p) := by nlinarith
  have hs1 : 4 * p * (1 - p) < 1 := by nlinarith [sq_nonneg (1 - 2 * p), mul_pos (by linarith : (0:ℝ) < 2*p - 1) (by linarith : (0:ℝ) < 2*p - 1)]
  have h1u : (1 : ℝ) - u < 1 := by linarith
  
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (x := ((1 - 4 * p * (1 - p)) * δ ^ (u / (2 - u))) / (4 * p * (1 - p)))
    (by positivity) h1u
  refine ⟨k + 1, by omega, ?_⟩
  rw [lt_div_iff₀ hs0] at hk
  have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  nlinarith [hk, hmono, hs0]


theorem lib_level1_mass_nonneg [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 ≤ 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ∧ 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
        ≤ 4 * p * (1 - p)
          * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  refine ⟨?_, lib_level1_mass_le hp0 hp1 φ hu0 hu1⟩
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun S _ => sq_nonneg _)

end StatMech.Probability
