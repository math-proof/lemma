import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.LevelInfluenceBound.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[lib_optimal_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/LevelInfluenceBound.lean)
-/
@[path]
private lemma lib_optimal_exponent_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : ℝ}
-- given
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (2 : ℝ) / (2 - u) - 1 = u / (2 - u) := by
-- proof
  apply StatMech.Probability.lib_optimal_exponent hu0 hu1

/--
[lib_level1_mass_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/LevelInfluenceBound.lean)
-/
@[path]
private lemma lib_level1_mass_le_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 4 * p * (1 - p) * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.lib_level1_mass_le hp0 hp1 φ hu0 hu1

/--
[lib_capped_optimal_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/LevelInfluenceBound.lean)
-/
@[path]
private lemma lib_capped_optimal_weight_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  4 * ∑ S : Finset ι, (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ 4 * p * (1 - p) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.lib_capped_optimal_weight hp0 hp1 φ hu0 hu1

/--
[lib_residue_iff_levelGe2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/LevelInfluenceBound.lean)
-/
@[path]
private lemma lib_residue_iff_levelGe2_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
  {k : ℕ}
  {B : ℝ}
-- given
  (hk : 1 ≤ k) :
-- imply
  (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ B) ↔ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ B - 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
-- proof
  apply StatMech.Probability.lib_residue_iff_levelGe2 φ hk

/--
[lib_levelGe2_discharges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/LevelInfluenceBound.lean)
-/
@[path]
private lemma lib_levelGe2_discharges_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : lib_levelGe2Residue q} :
-- imply
  dtr_lowDegreeResidue q := by
-- proof
  apply StatMech.Probability.lib_levelGe2_discharges H

/--
[lib_levelGe2_budget_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/LevelInfluenceBound.lean)
-/
@[path]
private lemma lib_levelGe2_budget_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  {p δ u : ℝ}
-- given
  (hphalf : 1 / 2 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (_hu1 : u < 1)
  (hδ0 : 0 < δ ^ (u / (2 - u))) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ 0 ≤ δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k - 4 * p * (1 - p) * δ ^ (u / (2 - u)) := by
-- proof
  apply StatMech.Probability.lib_levelGe2_budget_pos hphalf hp1 hu0 _hu1 hδ0

/--
[lib_level1_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/LevelInfluenceBound.lean)
-/
@[path]
private lemma lib_level1_mass_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  0 ≤ 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ∧ 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 4 * p * (1 - p) * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.lib_level1_mass_nonneg hp0 hp1 φ hu0 hu1


-- created on 2026-10-23
