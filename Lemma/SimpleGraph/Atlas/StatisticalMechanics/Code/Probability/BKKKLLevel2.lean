import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.BKKKLLevel2
open Finset Real Set StatMech StatMech.Probability


/--
[bkt2_capped_levelGe2_damped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_capped_levelGe2_damped_eq
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
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card), (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ 4 * p * (1 - p) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt2_capped_levelGe2_damped hp0 hp1 φ hu0 hu1

/--
[bkt2_damped_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_damped_le_target_eq
  [Fintype ι]
  [DecidableEq ι]
  {p u : ℝ}
  {d : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu1 : u < 1) :
-- imply
  ((1 - u) * (4 * p * (1 - p))) ^ (d - 1) ≤ (1 - u) ^ (d - 1) := by
-- proof
  apply StatMech.Probability.bkt2_damped_le_target hp0 hp1 hu1 d

/--
[bkt2_target_eq_damped_of_p_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_target_eq_damped_of_p_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : ℝ}
  {d : ℕ} :
-- imply
  (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = (1 - u) ^ (d - 1) := by
-- proof
  apply StatMech.Probability.bkt2_target_eq_damped_of_p_half d

/--
[bkt2_lowDegreeMaster_of_levelGe2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_lowDegreeMaster_of_levelGe2_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2_levelGe2MasterResidue q} :
-- imply
  bkt_lowDegreeMasterResidue q := by
-- proof
  apply StatMech.Probability.bkt2_lowDegreeMaster_of_levelGe2 H

/--
[bkt2_master_of_levelGe2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_master_of_levelGe2_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2_levelGe2MasterResidue q} :
-- imply
  pro_PBiasedMaster q := by
-- proof
  apply StatMech.Probability.bkt2_master_of_levelGe2 H

/--
[bkt2_levelGe2_of_remaining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_levelGe2_of_remaining_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2_RemainingGoal q} :
-- imply
  bkt2_levelGe2MasterResidue q := by
-- proof
  apply StatMech.Probability.bkt2_levelGe2_of_remaining H

/--
[bkt2_master_of_remaining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_master_of_remaining_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2_RemainingGoal q} :
-- imply
  pro_PBiasedMaster q := by
-- proof
  apply StatMech.Probability.bkt2_master_of_remaining H

/--
[bkt2_rhoOptimise_of_remaining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_rhoOptimise_of_remaining_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2_RemainingGoal q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.bkt2_rhoOptimise_of_remaining H

/--
[bkt2_truncDamped_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_truncDamped_le_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
  {k : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ 4 * p * (1 - p) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt2_truncDamped_le hp0 hp1 φ hu0 hu1 k

/--
[bkt2_weightGap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_weightGap_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {p u : ℝ}
  {d : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu1 : u < 1) :
-- imply
  0 ≤ (1 - u) ^ (d - 1) - ((1 - u) * (4 * p * (1 - p))) ^ (d - 1) := by
-- proof
  apply StatMech.Probability.bkt2_weightGap_nonneg hp0 hp1 hu1 d

/--
[bkt2_remaining_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2.lean)
-/
@[path]
private lemma bkt2_remaining_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1)
  (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * ((1 - u) ^ (S.card - 1) - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)) * (0 : ℝ) ^ 2 ≤ (4 * (ptn_sigma p) ^ 2) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) - (1 - u) ^ k) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) - 4 * ∑ _S ∈ univ.filter (fun S : Finset E => S.card = 1), (0 : ℝ) ^ 2 - 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * (0 : ℝ) ^ 2) := by
-- proof
  apply StatMech.Probability.bkt2_remaining_c0 hp0 hp1 hu0 hu1 hδ0


-- created on 2026-10-23
