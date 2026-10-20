import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.MaximumTermLeModulus
open Set
open Complex


/--
[wimanMaximumTerm_le_wimanMaximumModulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermLeModulus.lean)
-/
@[path]
private lemma wimanMaximumTerm_le_wimanMaximumModulus_eq
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hr : 0 < r) :
-- imply
  wimanMaximumTerm f r ≤ wimanMaximumModulus f r := by
-- proof
  apply Complex.wimanMaximumTerm_le_wimanMaximumModulus f hf hr


-- created on 2026-10-20
