import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.CurveLength

/--
[intervalIntegral.integral_norm_deriv_eq_integral_norm_derivWithin_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/CurveLength.lean)
-/
@[path]
private lemma integral_norm_deriv_eq_integral_norm_derivWithin_Icc_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E]
-- given
  {a b : ℝ} (hab : a ≤ b) (f : ℝ → E) :
-- imply
  (∫ t in a..b, ‖deriv f t‖) = ∫ t in a..b, ‖derivWithin f (Set.Icc a b) t‖ := by
-- proof
  apply intervalIntegral.integral_norm_deriv_eq_integral_norm_derivWithin_Icc f hab


/--
[ContDiffOn.eVariationOn_Icc_eq_ofReal_integral_norm_derivWithin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/CurveLength.lean)
-/
@[path]
private lemma contDiffOn_eVariationOn_Icc_eq_ofReal_integral_norm_derivWithin_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
-- given
  {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
-- imply
  eVariationOn γ (Set.Icc a b) =
    ENNReal.ofReal (∫ t in a..b, ‖derivWithin γ (Set.Icc a b) t‖) := by
-- proof
  apply ContDiffOn.eVariationOn_Icc_eq_ofReal_integral_norm_derivWithin hab hγ


/--
[curve_length_eq_integral_norm_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/CurveLength.lean)
-/
@[path]
private lemma curve_length_eq_integral_norm_deriv_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
-- given
  {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
-- imply
  eVariationOn γ (Set.Icc a b) = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
-- proof
  apply Real.Calculus.CurveLength.curve_length_eq_integral_norm_deriv hab hγ


-- created on 2026-10-09
