import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.FSPerEdge
open Finset Real Filter Topology intervalIntegral MeasureTheory StatMech StatMech.Probability


/--
[fpe_summand_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSPerEdge.lean)
-/
@[path]
private lemma fpe_summand_intervalIntegrable_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : ℝ}
  {cf : Finset ι → ℝ}
  {S : Finset ι} :
-- imply
  IntervalIntegrable (fun u => 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1) * cf S) MeasureTheory.volume 0 1 := by
-- proof
  apply StatMech.Probability.fpe_summand_intervalIntegrable A cf S

/--
[fpe_integral_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSPerEdge.lean)
-/
@[path]
private lemma fpe_integral_summand_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : ℝ}
  {cf : Finset ι → ℝ}
  {S : Finset ι} :
-- imply
  (∫ u in (0:ℝ)..1, 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1) * cf S) = (if S = ∅ then 0 else 4 * (A ^ (S.card - 1) / A) * cf S) := by
-- proof
  apply StatMech.Probability.fpe_integral_summand A cf S

/--
[fpe_integral_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSPerEdge.lean)
-/
@[path]
private lemma fpe_integral_lhs_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : ℝ}
  {cf : Finset ι → ℝ} :
-- imply
  (∫ u in (0:ℝ)..1, ∑ S : Finset ι, 4 * (S.card : ℝ) * (A ^ (S.card - 1) / A) * (1 - u) ^ (S.card - 1) * cf S) = 4 * ∑ S ∈ (univ.erase (∅ : Finset ι)), (A ^ (S.card - 1) / A) * cf S := by
-- proof
  apply StatMech.Probability.fpe_integral_lhs A cf

/--
[fpe_master_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSPerEdge.lean)
-/
@[path]
private lemma fpe_master_sub_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p))) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fpe_master_sub hp0 hp1 φ u hu0 hu1

/--
[fpe_dampedVarLogGain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSPerEdge.lean)
-/
@[path]
private lemma fpe_dampedVarLogGain_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  2 * (∑ S ∈ (univ.erase (∅ : Finset ι)), ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p))) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fpe_dampedVarLogGain hp0 hp1 φ

/--
[fpe_Q_eq_var_at_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSPerEdge.lean)
-/
@[path]
private lemma fpe_Q_eq_var_at_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  (∑ S ∈ (univ.erase (∅ : Finset ι)), ((4 * (1/2 : ℝ) * (1 - 1/2)) ^ (S.card - 1) / (4 * (1/2 : ℝ) * (1 - 1/2))) * (ptn_coeff (1/2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = OSSS.var (OSSS.bernoulliWeight (1/2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fpe_Q_eq_var_at_half φ

/--
[fpe_kklGain_at_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSPerEdge.lean)
-/
@[path]
private lemma fpe_kklGain_at_half_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight (1/2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1/2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight (1/2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fpe_kklGain_at_half φ


-- created on 2026-10-23
