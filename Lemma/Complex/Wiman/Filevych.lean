import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.Filevych
open Filter MeasureTheory Set
open Complex


/--
[tendsto_wimanMaximumTerm_exp_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/Filevych.lean)
-/
@[path]
private lemma tendsto_wimanMaximumTerm_exp_atTop_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  Tendsto (fun x : ℝ => wimanMaximumTerm f (Real.exp x)) atTop atTop := by
-- proof
  apply Complex.tendsto_wimanMaximumTerm_exp_atTop f hf htrans

/--
[exists_wiman_radius_two_thirds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/Filevych.lean)
-/
@[path]
private lemma exists_wiman_radius_two_thirds_eq
  {f : ℂ → ℂ}
  {R : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∃ r : ℝ, R < r ∧ wimanMaximumModulus f r ≤
    wimanMaximumTerm f r *
    Real.log (wimanMaximumTerm f r) ^ (2 / 3 : ℝ) := by
-- proof
  apply Complex.exists_wiman_radius_two_thirds f hf htrans R


-- created on 2026-10-20
