import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.InfiniteTaylorSupport
open Complex


/--
[infinite_support_wimanTaylorCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/InfiniteTaylorSupport.lean)
-/
@[path]
private lemma infinite_support_wimanTaylorCoefficient_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  (Function.support (wimanTaylorCoefficient f)).Infinite := by
-- proof
  apply Complex.infinite_support_wimanTaylorCoefficient f hf htrans


-- created on 2026-10-20
