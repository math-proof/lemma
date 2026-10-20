import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.MaximumModulusLeMajorant
open Complex


/--
[wimanMaximumModulus_le_wimanMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumModulusLeMajorant.lean)
-/
@[path]
private lemma wimanMaximumModulus_le_wimanMajorant_eq
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hr : 0 ≤ r) :
-- imply
  wimanMaximumModulus f r ≤ wimanMajorant f r := by
-- proof
  apply Complex.wimanMaximumModulus_le_wimanMajorant f hf hr


-- created on 2026-10-20
