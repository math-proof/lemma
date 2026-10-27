import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.DegreeTruncation.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[dtr_full_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_full_weight_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  4 * ∑ S : Finset ι, (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 = 4 * p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.dtr_full_weight_eq hp0 hp1 φ

/--
[dtr_pow_mono_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_pow_mono_exp_eq
  [Fintype ι]
  [DecidableEq ι]
  {x : ℝ}
  {k m : ℕ}
-- given
  (h0 : 0 ≤ x)
  (h1 : x ≤ 1)
  (hkm : k ≤ m) :
-- imply
  x ^ m ≤ x ^ k := by
-- proof
  apply StatMech.Probability.dtr_pow_mono_exp h0 h1 hkm

/--
[dtr_high_part_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_high_part_le_eq
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
  apply StatMech.Probability.dtr_high_part_le hp0 hp1 φ hu0 hu1 k

/--
[dtr_trunc_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_trunc_split_eq
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
  apply StatMech.Probability.dtr_trunc_split hp0 hp1 φ hu0 hu1 k

/--
[dtr_lowDegree_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_lowDegree_of_residue_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : dtr_lowDegreeResidue q} :
-- imply
  hcq_lowRangeResidue q := by
-- proof
  apply StatMech.Probability.dtr_lowDegree_of_residue H

/--
[dtr_smallDelta_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_smallDelta_of_residue_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : dtr_lowDegreeResidue q} :
-- imply
  cvg_smallDeltaResidue q := by
-- proof
  apply StatMech.Probability.dtr_smallDelta_of_residue H

/--
[dtr_martingaleHC_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_martingaleHC_of_residue_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : dtr_lowDegreeResidue q} :
-- imply
  mxd_martingaleHC_statement q := by
-- proof
  apply StatMech.Probability.dtr_martingaleHC_of_residue H

/--
[dtr_budget_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_budget_pos_eq
  [Fintype ι]
  [DecidableEq ι]
  {p δ u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (_hu1 : u < 1)
  (hδ0 : 0 < δ ^ (u / (2 - u))) :
-- imply
  ∃ k : ℕ, 0 ≤ δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k := by
-- proof
  apply StatMech.Probability.dtr_budget_pos hp0 hp1 hu0 _hu1 hδ0

/--
[dtr_residue_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_residue_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {u : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1)
  (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) :
-- imply
  ∃ k : ℕ, (0 : ℝ) ≤ ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.dtr_residue_c0 hp0 hp1 hu0 hu1 φ hδ0

/--
[dtr_high_part_proved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DegreeTruncation.lean)
-/
@[path]
private lemma dtr_high_part_proved_eq
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
  apply StatMech.Probability.dtr_high_part_proved hp0 hp1 φ hu0 hu1 k


-- created on 2026-10-23
