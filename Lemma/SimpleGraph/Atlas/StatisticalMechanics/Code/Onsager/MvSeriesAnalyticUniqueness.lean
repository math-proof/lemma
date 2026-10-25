import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.MvSeriesAnalyticUniqueness.Part3
open StatMech StatMech.Onsager


/--
[ons_mvMonomialValue_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean)
-/
@[path]
private lemma ons_mvMonomialValue_smul_eq
  [DecidableEq E]
  {s : ℂ}
  {weight : E → ℂ}
  {m : E →₀ ℕ} :
-- imply
  ons_mvMonomialValue (fun e ↦ s * weight e) m = s ^ Finsupp.degree m * ons_mvMonomialValue weight m := by
-- proof
  apply StatMech.Onsager.ons_mvMonomialValue_smul s weight m

/--
[ons_summable_degreeFiberNorm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean)
-/
@[path]
private lemma ons_summable_degreeFiberNorm_eq
  {series : MvPowerSeries E ℂ}
  {weight : E → ℂ}
-- given
  (hsum : ons_MvSeriesEvalSummable series weight) :
-- imply
  Summable (ons_degreeFiberNorm series weight) := by
-- proof
  apply StatMech.Onsager.ons_summable_degreeFiberNorm series weight hsum

/--
[ons_norm_degreeFiberCoeff_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean)
-/
@[path]
private lemma ons_norm_degreeFiberCoeff_le_eq
  {series : MvPowerSeries E ℂ}
  {weight : E → ℂ}
  {n : ℕ}
-- given
  (hsum : ons_MvSeriesEvalSummable series weight) :
-- imply
  ‖ons_degreeFiberCoeff series weight n‖ ≤ ons_degreeFiberNorm series weight n := by
-- proof
  apply StatMech.Onsager.ons_norm_degreeFiberCoeff_le series weight hsum n

/--
[ons_summable_norm_degreeFiberCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean)
-/
@[path]
private lemma ons_summable_norm_degreeFiberCoeff_eq
  {series : MvPowerSeries E ℂ}
  {weight : E → ℂ}
-- given
  (hsum : ons_MvSeriesEvalSummable series weight) :
-- imply
  Summable fun n ↦ ‖ons_degreeFiberCoeff series weight n‖ := by
-- proof
  apply StatMech.Onsager.ons_summable_norm_degreeFiberCoeff series weight hsum

/--
[ons_mvSeriesEval_smul_eq_degreeFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean)
-/
@[path]
private lemma ons_mvSeriesEval_smul_eq_degreeFiber_eq
  [Fintype E]
  [DecidableEq E]
  {series : MvPowerSeries E ℂ}
  {weight : E → ℂ}
  {s : ℂ}
-- given
  (hsum : ons_MvSeriesEvalSummable series weight)
  (hs : ‖s‖ ≤ 1) :
-- imply
  ons_mvSeriesEval series (fun e ↦ s * weight e) = ∑' n, ons_degreeFiberCoeff series weight n * s ^ n := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_smul_eq_degreeFiber series weight hsum s hs

/--
[ons_degreeFiberCoeff_eq_zero_of_eval_smul_eventually_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean)
-/
@[path]
private lemma ons_degreeFiberCoeff_eq_zero_of_eval_smul_eventually_zero_eq
  [Fintype E]
  [DecidableEq E]
  {series : MvPowerSeries E ℂ}
  {weight : E → ℂ}
  {n : ℕ}
-- given
  (hsum : ons_MvSeriesEvalSummable series weight)
  (hzero : ∀ᶠ s : ℂ in nhds 0, ons_mvSeriesEval series (fun e ↦ s * weight e) = 0) :
-- imply
  ons_degreeFiberCoeff series weight n = 0 := by
-- proof
  apply StatMech.Onsager.ons_degreeFiberCoeff_eq_zero_of_eval_smul_eventually_zero series weight hsum hzero n

/--
[ons_degreeFiberPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean)
-/
@[path]
private lemma ons_degreeFiberPolynomial_eval_eq
  [Fintype E]
  [DecidableEq E]
  {series : MvPowerSeries E ℂ}
  {weight : E → ℂ}
  {n : ℕ} :
-- imply
  MvPolynomial.eval weight (ons_degreeFiberPolynomial series n) = ons_degreeFiberCoeff series weight n := by
-- proof
  apply StatMech.Onsager.ons_degreeFiberPolynomial_eval series weight n

/--
[ons_coeff_eq_zero_of_degreeFiberCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean)
-/
@[path]
private lemma ons_coeff_eq_zero_of_degreeFiberCoeff_eq
  [Fintype E]
  [DecidableEq E]
  {series : MvPowerSeries E ℂ}
  {m : E →₀ ℕ}
-- given
  (hzero : ∀ weight : E → ℂ, ons_degreeFiberCoeff series weight (Finsupp.degree m) = 0) :
-- imply
  MvPowerSeries.coeff m series = 0 := by
-- proof
  apply StatMech.Onsager.ons_coeff_eq_zero_of_degreeFiberCoeff series m hzero


-- created on 2026-10-23
