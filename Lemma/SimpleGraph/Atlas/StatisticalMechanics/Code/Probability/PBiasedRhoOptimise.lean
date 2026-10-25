import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.PBiasedRhoOptimise
open Finset Real Filter Topology StatMech StatMech.OSSS StatMech.Probability


/--
[pro_degreeWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedRhoOptimise.lean)
-/
@[path]
private lemma pro_degreeWeight_eq_eq
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S : Finset E, 4 * (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 4 * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.pro_degreeWeight_eq hp0 hp1 φ

/--
[pro_rhoOptimise_of_master](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedRhoOptimise.lean)
-/
@[path]
private lemma pro_rhoOptimise_of_master_eq
  {q : ℝ}
  {H : pro_PBiasedMaster q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.pro_rhoOptimise_of_master H

/--
[pro_master_lhs_zero_of_totalInfl_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedRhoOptimise.lean)
-/
@[path]
private lemma pro_master_lhs_zero_of_totalInfl_zero_eq
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hT : totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
-- imply
  (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 0 := by
-- proof
  apply StatMech.Probability.pro_master_lhs_zero_of_totalInfl_zero hp0 hp1 φ hT u

/--
[pro_master_holds_of_totalInfl_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedRhoOptimise.lean)
-/
@[path]
private lemma pro_master_holds_of_totalInfl_zero_eq
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hT : totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
-- imply
  (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * (4 * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.pro_master_holds_of_totalInfl_zero hp0 hp1 φ hT u


-- created on 2026-10-23
