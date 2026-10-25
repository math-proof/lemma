import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
open Finset Real Filter Topology intervalIntegral MeasureTheory StatMech StatMech.Probability


/--
[cro2_integral_exp_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_integral_exp_mul_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {a b : ℝ}
-- given
  (hc : c ≠ 0) :
-- imply
  ∫ x in a..b, Real.exp (c * x) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
-- proof
  apply StatMech.Probability.cro2_integral_exp_mul c hc a b

/--
[cro2_integral_exp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_integral_exp_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  (∫ u in (0:ℝ)..1, Real.exp (-(t / 2) * u)) ≤ 2 / t := by
-- proof
  apply StatMech.Probability.cro2_integral_exp_le t ht

/--
[cro2_integral_one_sub_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_integral_one_sub_pow_eq
  [Fintype ι]
  [DecidableEq ι]
  {n : ℕ} :
-- imply
  ∫ u in (0:ℝ)..1, (1 - u) ^ n = 1 / (n + 1) := by
-- proof
  apply StatMech.Probability.cro2_integral_one_sub_pow n

/--
[cro2_summand_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_summand_intervalIntegrable_eq
  [Fintype ι]
  [DecidableEq ι]
  {cf : Finset ι → ℝ}
  {S : Finset ι} :
-- imply
  IntervalIntegrable (fun u => 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S) MeasureTheory.volume 0 1 := by
-- proof
  apply StatMech.Probability.cro2_summand_intervalIntegrable cf S

/--
[cro2_integral_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_integral_summand_eq
  [Fintype ι]
  [DecidableEq ι]
  {cf : Finset ι → ℝ}
  {S : Finset ι} :
-- imply
  (∫ u in (0:ℝ)..1, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S) = (if S = ∅ then 0 else 4 * cf S) := by
-- proof
  apply StatMech.Probability.cro2_integral_summand cf S

/--
[cro2_integral_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_integral_lhs_eq
  [Fintype ι]
  [DecidableEq ι]
  {cf : Finset ι → ℝ} :
-- imply
  (∫ u in (0:ℝ)..1, ∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S) = 4 * ∑ S ∈ (univ.erase (∅ : Finset ι)), cf S := by
-- proof
  apply StatMech.Probability.cro2_integral_lhs cf

/--
[cro2_rpow_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_rpow_integrable_eq
  [Fintype ι]
  [DecidableEq ι]
  {δ : ℝ}
-- given
  (hδ0 : 0 < δ) :
-- imply
  IntervalIntegrable (fun u => δ ^ (u / (2 - u))) MeasureTheory.volume 0 1 := by
-- proof
  apply StatMech.Probability.cro2_rpow_integrable δ hδ0

/--
[cro2_integral_rhs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_integral_rhs_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {δ : ℝ}
-- given
  (hδ0 : 0 < δ)
  (hδ1 : δ < 1) :
-- imply
  (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u))) ≤ 2 / (-(Real.log δ)) := by
-- proof
  apply StatMech.Probability.cro2_integral_rhs_le δ hδ0 hδ1

/--
[cro2_master_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_master_sub_eq
  [Fintype ι]
  [DecidableEq ι]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
-- given
  (Hcap : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → (∑ S : Finset E, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2) - 1) * (∑ S : Finset E, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2))
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * (∑ S : Finset E, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
-- proof
  apply StatMech.Probability.cro2_master_sub φ Hcap u hu0 hu1

/--
[cro2_rhoOptimise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseClose2.lean)
-/
@[path]
private lemma cro2_rhoOptimise_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  bph_RhoOptimise 2 := by
-- proof
  apply StatMech.Probability.cro2_rhoOptimise


-- created on 2026-10-23
