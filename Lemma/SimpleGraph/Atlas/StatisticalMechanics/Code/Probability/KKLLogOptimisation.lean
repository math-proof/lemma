import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.KKLLogOptimisation
open Finset Real Filter Topology StatMech StatMech.Probability


/--
[klo_indicator_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_indicator_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {ω : ConfigSpace ι} :
-- imply
  ((fun ω => if φ ω then (1 : ℝ) else 0) ω) ^ 2 = (fun ω => if φ ω then (1 : ℝ) else 0) ω := by
-- proof
  apply StatMech.Probability.klo_indicator_sq φ ω

/--
[klo_uexp_sq_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_uexp_sq_eq_mean_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  bnt_uexp (fun x => ((fun ω => if φ ω then (1 : ℝ) else 0) x) ^ 2) = bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.klo_uexp_sq_eq_mean φ

/--
[klo_var_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_var_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  (∑ S ∈ (univ.erase (∅ : Finset ι)), (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
-- proof
  apply StatMech.Probability.klo_var_eq φ

/--
[klo_one_sub_pow_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_one_sub_pow_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {x : ℝ}
  {k : ℕ}
-- given
  (h0 : 0 ≤ x)
  (h1 : x ≤ 1) :
-- imply
  1 - x ^ k ≤ (1 - x) * k := by
-- proof
  apply StatMech.Probability.klo_one_sub_pow_le x h0 h1 k

/--
[klo_one_sub_rhopow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_one_sub_rhopow_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {k : ℕ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  1 - (ρ ^ k) ^ 2 ≤ (1 - ρ ^ 2) * k := by
-- proof
  apply StatMech.Probability.klo_one_sub_rhopow ρ h0 h1 k

/--
[klo_var_sub_damped_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_var_sub_damped_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {ρ : ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (∑ S ∈ (univ.erase (∅ : Finset ι)), (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) - (∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (1 - ρ ^ 2) * (∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4 := by
-- proof
  apply StatMech.Probability.klo_var_sub_damped_le φ ρ h0 h1

/--
[klo_master_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_master_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {ρ : ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2)) ≤ (1 - ρ ^ 2) * (∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4 := by
-- proof
  apply StatMech.Probability.klo_master_le φ ρ h0 h1

/--
[klo_master_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_master_sub_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hu0 : 0 < u)
  (hu1 : u ≤ 1) :
-- imply
  bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (1 / (1 - u / 2)) ≤ u * ((∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4) := by
-- proof
  apply StatMech.Probability.klo_master_sub φ u hu0 hu1

/--
[klo_edge_isoperimetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_edge_isoperimetric_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
-- given
  (hm0 : 0 < bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) :
-- imply
  2 * bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ ∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.klo_edge_isoperimetric φ hm0

/--
[klo_deltaUpgrade_hyp_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_deltaUpgrade_hyp_holds_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2)) ≤ (1 - ρ ^ 2) * (∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4 := by
-- proof
  apply StatMech.Probability.klo_deltaUpgrade_hyp_holds φ

/--
[klo_deltaUpgrade_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_deltaUpgrade_zero_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  klo_DeltaUpgrade 0 := by
-- proof
  apply StatMech.Probability.klo_deltaUpgrade_zero

/--
[klo_logOptimisation_of_deltaUpgrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_logOptimisation_of_deltaUpgrade_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {H : klo_DeltaUpgrade c} :
-- imply
  kls_LogOptimisation c := by
-- proof
  apply StatMech.Probability.klo_logOptimisation_of_deltaUpgrade H

/--
[klo_logOptimisation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogOptimisation.lean)
-/
@[path]
private lemma klo_logOptimisation_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {H : klo_DeltaUpgrade c} :
-- imply
  KKLHypercontractive (1 / 2 : ℝ) c := by
-- proof
  apply StatMech.Probability.klo_logOptimisation H


-- created on 2026-10-23
