import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.TaylorExpansion
open Complex


/--
[hasSum_wimanTaylorCoefficient_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/TaylorExpansion.lean)
-/
@[path]
private lemma hasSum_wimanTaylorCoefficient_mul_pow_eq
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  HasSum (fun n : ℕ => wimanTaylorCoefficient f n * z ^ n) (f z) := by
-- proof
  apply Complex.hasSum_wimanTaylorCoefficient_mul_pow f hf z


-- created on 2026-10-20
