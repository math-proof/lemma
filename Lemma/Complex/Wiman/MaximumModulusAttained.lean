import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.MaximumModulusAttained
open Set
open Complex


/--
[exists_mem_sphere_eq_wimanMaximumModulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumModulusAttained.lean)
-/
@[path]
private lemma exists_mem_sphere_eq_wimanMaximumModulus_eq
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (hr : 0 ≤ r) :
-- imply
  ∃ z ∈ Metric.sphere (0 : ℂ) r,
    wimanMaximumModulus f r = ‖f z‖ ∧
    ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖f w‖ ≤ ‖f z‖ := by
-- proof
  apply Complex.exists_mem_sphere_eq_wimanMaximumModulus f hf hr


-- created on 2026-10-20
