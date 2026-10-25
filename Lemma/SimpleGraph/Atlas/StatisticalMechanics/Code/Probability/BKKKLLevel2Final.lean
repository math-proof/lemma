import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.BKKKLLevel2Final.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[fs_lever](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma fs_lever_eq
  [Fintype ι]
  [DecidableEq ι]
  {x y : ℝ}
  {m : ℕ}
-- given
  (hx : 0 ≤ x)
  (hxy : x ≤ y) :
-- imply
  (m : ℝ) * x ^ (m - 1) * (y - x) ≤ y ^ m - x ^ m := by
-- proof
  apply StatMech.Probability.fs_lever hx hxy m

/--
[fs_degree_to_undegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma fs_degree_to_undegree_eq
  [Fintype ι]
  [DecidableEq ι]
  {u u' : ℝ}
  {m : ℕ}
-- given
  (hu1 : u < 1)
  (hlt : u' < u) :
-- imply
  (m : ℝ) * (1 - u) ^ (m - 1) ≤ (1 - u') ^ m / (u - u') := by
-- proof
  apply StatMech.Probability.fs_degree_to_undegree hu1 hlt m

/--
[bkt2f_targetWeight_levelGe2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_targetWeight_levelGe2_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u' : ℝ}
  {k : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu'0 : 0 < u')
  (hu'1 : u' < 1)
  (hcap : 1 - u' ≤ 4 * p * (1 - p)) :
-- imply
  ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p))) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
-- proof
  apply StatMech.Probability.bkt2f_targetWeight_levelGe2 hp0 hp1 φ hu'0 hu'1 hcap k

/--
[bkt2f_degreeWeight_le_undegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_degreeWeight_le_undegree_eq
  [Fintype ι]
  [DecidableEq ι]
  {u u' : ℝ}
  {φ : ConfigSpace ι → Bool}
  {p : ℝ}
  {k : ℕ}
-- given
  (hu1 : u < 1)
  (hlt : u' < u) :
-- imply
  ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ (1 / (u - u')) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.bkt2f_degreeWeight_le_undegree hu1 hlt φ k

/--
[bkt2f_FS_highDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_FS_highDegree_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u u' : ℝ}
  {k : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu1 : u < 1)
  (hu'0 : 0 < u')
  (hlt : u' < u)
  (hcap : 1 - u' ≤ 4 * p * (1 - p)) :
-- imply
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ (4 / (u - u')) * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p))) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
-- proof
  apply StatMech.Probability.bkt2f_FS_highDegree hp0 hp1 φ hu1 hu'0 hlt hcap k

/--
[bkt2f_qnormPow_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_qnormPow_indicator_eq
  [Fintype ι]
  [DecidableEq ι]
  {p q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hq : 0 < q) :
-- imply
  ptn_qnormPow p q (fun ω => if φ ω then (1 : ℝ) else 0) = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.bkt2f_qnormPow_indicator hq φ

/--
[bkt2f_qnorm_indicator_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_qnorm_indicator_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq : 0 < q) :
-- imply
  (ptn_qnorm p q (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 = (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((2 : ℝ) / q) := by
-- proof
  apply StatMech.Probability.bkt2f_qnorm_indicator_sq hp0 hp1 hq φ

/--
[bkt2f_levelGe2_of_meanInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_levelGe2_of_meanInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2f_meanInflResidue q} :
-- imply
  bkt2_levelGe2MasterResidue q := by
-- proof
  apply StatMech.Probability.bkt2f_levelGe2_of_meanInfl H

/--
[bkt2f_remaining_of_meanInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_remaining_of_meanInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2f_meanInflResidue q} :
-- imply
  bkt2_RemainingGoal q := by
-- proof
  apply StatMech.Probability.bkt2f_remaining_of_meanInfl H

/--
[bkt2f_master_of_meanInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_master_of_meanInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2f_meanInflResidue q} :
-- imply
  pro_PBiasedMaster q := by
-- proof
  apply StatMech.Probability.bkt2f_master_of_meanInfl H

/--
[bkt2f_rhoOptimise_of_meanInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_rhoOptimise_of_meanInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt2f_meanInflResidue q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.bkt2f_rhoOptimise_of_meanInfl H

/--
[bkt2f_meanInflResidue_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_meanInflResidue_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {u : ℝ}
-- given
  (hp : 1 / 2 < p)
  (hp1 : p < 1)
  (hu1 : u < 1)
  (hcap : 1 - 4 * p * (1 - p) < u)
  (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) :
-- imply
  ∃ u' : ℝ, 0 < u' ∧ u' < u ∧ 1 - u' ≤ 4 * p * (1 - p) ∧ ∃ k : ℕ, 1 ≤ k ∧ (4 / (u - u')) * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p))) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ 2 ≤ (4 * (ptn_sigma p) ^ 2) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) - (1 - u) ^ k) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1), (ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.bkt2f_meanInflResidue_c0 hp hp1 hu1 hcap hδ0

/--
[bkt2f_gap_vanishes_at_p_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Final.lean)
-/
@[path]
private lemma bkt2f_gap_vanishes_at_p_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : ℝ}
  {d : ℕ} :
-- imply
  (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 := by
-- proof
  apply StatMech.Probability.bkt2f_gap_vanishes_at_p_half d


-- created on 2026-10-23
