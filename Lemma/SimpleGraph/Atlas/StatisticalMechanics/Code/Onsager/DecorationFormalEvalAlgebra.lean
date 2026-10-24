import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationFormalEvalAlgebra
open StatMech StatMech.Onsager


/--
[ons_mvMonomialValue_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvMonomialValue_add_eq
  [DecidableEq E]
  {weight : E → ℂ}
  {m n : E →₀ ℕ} :
-- imply
  ons_mvMonomialValue weight (m + n) = ons_mvMonomialValue weight m * ons_mvMonomialValue weight n := by
-- proof
  apply StatMech.Onsager.ons_mvMonomialValue_add weight m n

/--
[ons_mvSeriesEval_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvSeriesEval_eq_eq
  {series : MvPowerSeries E ℂ}
  {weight : E → ℂ} :
-- imply
  ons_mvSeriesEval series weight = ∑' m : E →₀ ℕ, MvPowerSeries.coeff m series * ons_mvMonomialValue weight m := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_eq series weight

/--
[ons_MvSeriesEvalSummable.mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma mul_eq
  [DecidableEq E]
  {f g : MvPowerSeries E ℂ}
  {weight : E → ℂ}
-- given
  (hf : ons_MvSeriesEvalSummable f weight)
  (hg : ons_MvSeriesEvalSummable g weight) :
-- imply
  ons_MvSeriesEvalSummable (f * g) weight := by
-- proof
  apply StatMech.Onsager.ons_MvSeriesEvalSummable.mul hf hg

/--
[ons_mvSeriesEval_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvSeriesEval_mul_eq
  [DecidableEq E]
  {f g : MvPowerSeries E ℂ}
  {weight : E → ℂ}
-- given
  (hf : ons_MvSeriesEvalSummable f weight)
  (hg : ons_MvSeriesEvalSummable g weight) :
-- imply
  ons_mvSeriesEval (f * g) weight = ons_mvSeriesEval f weight * ons_mvSeriesEval g weight := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_mul hf hg

/--
[ons_mvSeriesEvalNorm_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvSeriesEvalNorm_mul_le_eq
  [DecidableEq E]
  {f g : MvPowerSeries E ℂ}
  {weight : E → ℂ}
-- given
  (hf : ons_MvSeriesEvalSummable f weight)
  (hg : ons_MvSeriesEvalSummable g weight) :
-- imply
  ons_mvSeriesEvalNorm (f * g) weight ≤ ons_mvSeriesEvalNorm f weight * ons_mvSeriesEvalNorm g weight := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEvalNorm_mul_le hf hg

/--
[ons_MvSeriesEvalSummable.one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma one_eq
  [DecidableEq E]
  {weight : E → ℂ} :
-- imply
  ons_MvSeriesEvalSummable (1 : MvPowerSeries E ℂ) weight := by
-- proof
  apply StatMech.Onsager.ons_MvSeriesEvalSummable.one weight

/--
[ons_mvSeriesEval_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvSeriesEval_one_eq
  [DecidableEq E]
  {weight : E → ℂ} :
-- imply
  ons_mvSeriesEval (1 : MvPowerSeries E ℂ) weight = 1 := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_one weight

/--
[ons_mvSeriesEvalNorm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvSeriesEvalNorm_one_eq
  [DecidableEq E]
  {weight : E → ℂ} :
-- imply
  ons_mvSeriesEvalNorm (1 : MvPowerSeries E ℂ) weight = 1 := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEvalNorm_one weight

/--
[ons_MvSeriesEvalSummable.pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma pow_eq
  [DecidableEq E]
  {f : MvPowerSeries E ℂ}
  {weight : E → ℂ}
  {n : ℕ}
-- given
  (hf : ons_MvSeriesEvalSummable f weight) :
-- imply
  ons_MvSeriesEvalSummable (f ^ n) weight := by
-- proof
  apply StatMech.Onsager.ons_MvSeriesEvalSummable.pow hf n

/--
[ons_mvSeriesEval_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvSeriesEval_pow_eq
  [DecidableEq E]
  {f : MvPowerSeries E ℂ}
  {weight : E → ℂ}
  {n : ℕ}
-- given
  (hf : ons_MvSeriesEvalSummable f weight) :
-- imply
  ons_mvSeriesEval (f ^ n) weight = ons_mvSeriesEval f weight ^ n := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_pow hf n

/--
[ons_mvSeriesEvalNorm_pow_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvSeriesEvalNorm_pow_le_eq
  [DecidableEq E]
  {f : MvPowerSeries E ℂ}
  {weight : E → ℂ}
  {n : ℕ}
-- given
  (hf : ons_MvSeriesEvalSummable f weight) :
-- imply
  ons_mvSeriesEvalNorm (f ^ n) weight ≤ ons_mvSeriesEvalNorm f weight ^ n := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEvalNorm_pow_le hf n

/--
[ons_powerSeries_exp_coeff_complex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_powerSeries_exp_coeff_complex_eq
  {n : ℕ} :
-- imply
  PowerSeries.coeff n (PowerSeries.exp ℂ) = (1 : ℂ) / (n.factorial : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_powerSeries_exp_coeff_complex n

/--
[ons_MvSeriesEvalSummable_subst_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_MvSeriesEvalSummable_subst_exp_eq
  [DecidableEq E]
  {f : MvPowerSeries E ℂ}
  {weight : E → ℂ}
-- given
  (hsubst : PowerSeries.HasSubst f)
  (hf : ons_MvSeriesEvalSummable f weight) :
-- imply
  ons_MvSeriesEvalSummable (PowerSeries.subst f (PowerSeries.exp ℂ)) weight := by
-- proof
  apply StatMech.Onsager.ons_MvSeriesEvalSummable_subst_exp f weight hsubst hf

/--
[ons_mvSeriesEval_subst_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean)
-/
@[path]
private lemma ons_mvSeriesEval_subst_exp_eq
  [DecidableEq E]
  {f : MvPowerSeries E ℂ}
  {weight : E → ℂ}
-- given
  (hsubst : PowerSeries.HasSubst f)
  (hf : ons_MvSeriesEvalSummable f weight) :
-- imply
  ons_mvSeriesEval (PowerSeries.subst f (PowerSeries.exp ℂ)) weight = Complex.exp (ons_mvSeriesEval f weight) := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_subst_exp f weight hsubst hf


-- created on 2026-10-23
