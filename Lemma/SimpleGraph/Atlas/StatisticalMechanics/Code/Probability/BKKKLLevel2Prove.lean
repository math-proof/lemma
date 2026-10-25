import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.BKKKLLevel2Prove.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[bkt2p_undegree_le_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_undegree_le_var_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u' : ℝ}
  {k : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu'0 : 0 ≤ u')
  (hu'1 : u' < 1) :
-- imply
  ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt2p_undegree_le_var hp0 hp1 φ hu'0 hu'1 k

/--
[bkt2p_levelGe2_le_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_levelGe2_le_var_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u u' : ℝ}
  {k : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu1 : u < 1)
  (hu'0 : 0 ≤ u')
  (hlt : u' < u) :
-- imply
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ (4 / (u - u')) * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
-- proof
  apply StatMech.Probability.bkt2p_levelGe2_le_var hp0 hp1 φ hu1 hu'0 hlt k

/--
[bkt2p_levelGe2_of_varGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_levelGe2_of_varGap_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2p_VarGapCore q} :
-- imply
  bkt2_levelGe2MasterResidue q := by
-- proof
  apply StatMech.Probability.bkt2p_levelGe2_of_varGap H

/--
[bkt2p_remaining_of_varGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_remaining_of_varGap_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2p_VarGapCore q} :
-- imply
  bkt2_RemainingGoal q := by
-- proof
  apply StatMech.Probability.bkt2p_remaining_of_varGap H

/--
[bkt2p_master_of_varGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_master_of_varGap_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2p_VarGapCore q} :
-- imply
  pro_PBiasedMaster q := by
-- proof
  apply StatMech.Probability.bkt2p_master_of_varGap H

/--
[bkt2p_rhoOptimise_of_varGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_rhoOptimise_of_varGap_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2p_VarGapCore q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.bkt2p_rhoOptimise_of_varGap H

/--
[bkt2p_varGapCore_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_varGapCore_c0_eq
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
  ∃ u' : ℝ, 0 < u' ∧ u' < u ∧ ∃ k : ℕ, 1 ≤ k ∧ (4 / (u - u')) * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))) ≤ (4 * (ptn_sigma p) ^ 2) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) - (1 - u) ^ k) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1), (ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.bkt2p_varGapCore_c0 hp0 hp1 hu0 hu1 hδ0

/--
[bkt2p_levelGe2_le_var_and_mil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_levelGe2_le_var_and_mil_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u u' : ℝ}
  {k : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1)
  (hu'0 : 0 ≤ u')
  (hlt : u' < u) :
-- imply
  (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ (4 / (u - u')) * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) ∧ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 4 * (k : ℝ) * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) := by
-- proof
  apply StatMech.Probability.bkt2p_levelGe2_le_var_and_mil hp0 hp1 φ hu0 hu1 hu'0 hlt k

/--
[bkt2p_poincare_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_poincare_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.bkt2p_poincare_half hp0 hp1 φ

/--
[bkt2p_gap_vanishes_at_p_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean)
-/
@[path]
private lemma bkt2p_gap_vanishes_at_p_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : ℝ}
  {d : ℕ} :
-- imply
  (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 := by
-- proof
  apply StatMech.Probability.bkt2p_gap_vanishes_at_p_half d


-- created on 2026-10-23
