import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.BKKKLTruncation.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[bkt_high_part_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_high_part_decay_eq
  [Fintype ι]
  [DecidableEq ι]
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
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ (1 - u) ^ k * (4 * p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt_high_part_decay hp0 hp1 φ hu0 hu1 k

/--
[bkt_trunc_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_trunc_split_eq
  [Fintype ι]
  [DecidableEq ι]
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
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) + (1 - u) ^ k * (4 * p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt_trunc_split hp0 hp1 φ hu0 hu1 k

/--
[bkt_lhs_eq_level1_of_degree1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_lhs_eq_level1_of_degree1_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hdeg : ∀ S : Finset ι, 2 ≤ S.card → ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S = 0) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.bkt_lhs_eq_level1_of_degree1 φ u hdeg

/--
[bkt_level1_endpoint_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_level1_endpoint_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 4 * p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.bkt_level1_endpoint_zero hp0 hp1 φ

/--
[bkt_level1_endpoint_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_level1_endpoint_one_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 4 * p * (1 - p) * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.bkt_level1_endpoint_one hp0 hp1 φ

/--
[bkt_master_degree1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_master_degree1_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hdeg : ∀ S : Finset ι, 2 ≤ S.card → ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S = 0)
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * (4 * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt_master_degree1 hp0 hp1 φ hdeg hu0 hu1

/--
[bkt_master_endpoint_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_master_endpoint_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (0:ℝ)) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((0:ℝ) / (2 - 0)) * (4 * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt_master_endpoint_zero hp0 hp1 φ

/--
[bkt_master_endpoint_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_master_endpoint_one_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (1:ℝ)) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((1:ℝ) / (2 - 1)) * (4 * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt_master_endpoint_one hp0 hp1 φ

/--
[bkt_master_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_master_of_residue_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : bkt_lowDegreeMasterResidue q} :
-- imply
  pro_PBiasedMaster q := by
-- proof
  apply StatMech.Probability.bkt_master_of_residue H

/--
[bkt_budget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_budget_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : ℝ}
  {δ : ℝ}
-- given
  (hu0 : 0 < u)
  (_hu1 : u < 1)
  (hδ0 : 0 < δ ^ (u / (2 - u))) :
-- imply
  ∃ k : ℕ, 0 ≤ δ ^ (u / (2 - u)) - (1 - u) ^ k := by
-- proof
  apply StatMech.Probability.bkt_budget_nonneg hu0 _hu1 hδ0

/--
[bkt_residue_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_residue_c0_eq
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
  ∃ k : ℕ, 4 * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (0 : ℝ) ^ 2 ≤ (4 * (ptn_sigma p) ^ 2) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) - (1 - u) ^ k) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.bkt_residue_c0 hp0 hp1 hu0 hu1 hδ0

/--
[bkt_master_holds_degree1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_master_holds_degree1_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hdeg : ∀ S : Finset ι, 2 ≤ S.card → ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S = 0)
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * (4 * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.bkt_master_holds_degree1 hp0 hp1 φ hdeg hu0 hu1

/--
[bkt_degree1_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLTruncation.lean)
-/
@[path]
private lemma bkt_degree1_witness_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ} :
-- imply
  ∀ S : Finset ι, 2 ≤ S.card → ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) S = 0 := by
-- proof
  apply StatMech.Probability.bkt_degree1_witness p


-- created on 2026-10-23
