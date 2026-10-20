import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.MaximumTermTendsToInfinity
open Filter
open Complex


/--
[tendsto_wimanMaximumTerm_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermTendsToInfinity.lean)
-/
@[path]
private lemma tendsto_wimanMaximumTerm_atTop_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  Tendsto (wimanMaximumTerm f) atTop atTop := by
-- proof
  apply Complex.tendsto_wimanMaximumTerm_atTop f hf htrans

/--
[eventually_one_lt_wimanMaximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermTendsToInfinity.lean)
-/
@[path]
private lemma eventually_one_lt_wimanMaximumTerm_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∀ᶠ r : ℝ in atTop, 1 < wimanMaximumTerm f r := by
-- proof
  apply Complex.eventually_one_lt_wimanMaximumTerm f hf htrans

/--
[eventually_pos_log_wimanMaximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermTendsToInfinity.lean)
-/
@[path]
private lemma eventually_pos_log_wimanMaximumTerm_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∀ᶠ r : ℝ in atTop, 0 < Real.log (wimanMaximumTerm f r) := by
-- proof
  apply Complex.eventually_pos_log_wimanMaximumTerm f hf htrans


-- created on 2026-10-20
