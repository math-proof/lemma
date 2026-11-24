import Mathlib
import Notation.Algebra.Power
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.OUSemigroup
open GaussianSpace ProbabilityTheory MeasureTheory Real ContinuousLinearMap


/--
[gaussian_sum_pushforward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/OUSemigroup.lean)
-/
@[path]
private lemma main
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {a b c : ℝ}
-- given
  (habc : a² + b² = c²) :
-- imply
  ((stdGaussian E).prod (stdGaussian E)).map (addSmulCLM a b) = (stdGaussian E).map (c • ContinuousLinearMap.id ℝ E) := by
-- proof
  apply Measure.ext_of_charFunDual
  ext L'
  rw [charFunDual_map, charFunDual_prod]
  have h1 : (L'.comp (addSmulCLM (E := E) a b)).comp (ContinuousLinearMap.inl ℝ E E) = a • L' := by
    ext x; simp [addSmulCLM]
  have h2 : (L'.comp (addSmulCLM (E := E) a b)).comp (ContinuousLinearMap.inr ℝ E E) = b • L' := by
    ext x; simp [addSmulCLM]
  rw [h1, h2, charFunDual_stdGaussian, charFunDual_stdGaussian]
  rw [charFunDual_map]
  have h3 : L'.comp (c • ContinuousLinearMap.id ℝ E) = c • L' := by
    ext x; simp
  rw [h3, charFunDual_stdGaussian]
  simp only [norm_smul, Real.norm_eq_abs]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have ha : (|a| : ℝ)² = a² := sq_abs a
  have hb : (|b| : ℝ)² = b² := sq_abs b
  have hc : (|c| : ℝ)² = c² := sq_abs c
  have key : |a|² * ‖L'‖² + |b|² * ‖L'‖² = |c|² * ‖L'‖² := by
    nlinarith [habc]
  norm_cast
  linarith


lemma GaussianSpace.gaussian_sum_pushforward
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {a b c : ℝ}
-- given
  (habc : a² + b² = c²) :
-- imply
  ((stdGaussian E).prod (stdGaussian E)).map (addSmulCLM a b) = (stdGaussian E).map (c • ContinuousLinearMap.id ℝ E) :=
-- proof
  main habc


-- created on 2026-10-23
-- updated on 2026-11-24
