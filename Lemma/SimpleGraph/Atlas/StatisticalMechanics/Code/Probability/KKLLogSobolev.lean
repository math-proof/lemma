import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.KKLLogSobolev.Part2
open Finset StatMech StatMech.Probability


/--
[kls_indicator_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_indicator_rpow_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {φ : ConfigSpace ι → Bool}
  {ω : ConfigSpace ι}
-- given
  (hq : 0 < q) :
-- imply
  |(fun ω => if φ ω then (1 : ℝ) else 0) ω| ^ q = (fun ω => if φ ω then (1 : ℝ) else 0) ω := by
-- proof
  apply StatMech.Probability.kls_indicator_rpow hq φ ω

/--
[kls_qnormPow_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_qnormPow_indicator_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hq : 0 < q) :
-- imply
  bnt_qnormPow q (fun ω => if φ ω then (1 : ℝ) else 0) = bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.kls_qnormPow_indicator hq φ

/--
[kls_mean_eq_coeff_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_mean_eq_coeff_empty_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0) = khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) ∅ := by
-- proof
  apply StatMech.Probability.kls_mean_eq_coeff_empty φ

/--
[kls_qnorm_indicator_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_qnorm_indicator_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {φ : ConfigSpace ι → Bool} :
-- imply
  (bnt_qnorm (1 + ρ ^ 2) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 = (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.kls_qnorm_indicator_sq φ

/--
[kls_fluctWeight_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_fluctWeight_le_pow_eq
  [Fintype ι]
  [DecidableEq ι]
  {ρ : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  (∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2)) - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
-- proof
  apply StatMech.Probability.kls_fluctWeight_le_pow h0 h1 φ

/--
[kls_var_nonneg_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_var_nonneg_fourier_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  0 ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)), (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.kls_var_nonneg_fourier φ

/--
[kls_W_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_W_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  0 ≤ ∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.kls_W_nonneg φ

/--
[kls_var_le_W](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_var_le_W_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  (∑ S ∈ (univ.erase (∅ : Finset ι)), (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ ∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.kls_var_le_W φ

/--
[kls_fourierInflWeight_le_maxInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_fourierInflWeight_le_maxInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S), 4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.kls_fourierInflWeight_le_maxInfl φ e

/--
[kls_logOptimisation_hyp_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_logOptimisation_hyp_holds_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → (∑ S ∈ (univ.erase (∅ : Finset ι)), (ρ ^ S.card) ^ 2 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2)) - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
-- proof
  apply StatMech.Probability.kls_logOptimisation_hyp_holds φ

/--
[kls_logOptimisation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_logOptimisation_zero_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  kls_LogOptimisation 0 := by
-- proof
  apply StatMech.Probability.kls_logOptimisation_zero

/--
[kls_logOptimisation_implies_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_logOptimisation_implies_step_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {H : kls_LogOptimisation c} :
-- imply
  khc_LogSobolevStep c := by
-- proof
  apply StatMech.Probability.kls_logOptimisation_implies_step H

/--
[kls_logSobolevStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLLogSobolev.lean)
-/
@[path]
private lemma kls_logSobolevStep_eq
  [Fintype ι]
  [DecidableEq ι]
  {c : ℝ}
  {H : kls_LogOptimisation c} :
-- imply
  KKLHypercontractive (1 / 2 : ℝ) c := by
-- proof
  apply StatMech.Probability.kls_logSobolevStep H


-- created on 2026-10-23
