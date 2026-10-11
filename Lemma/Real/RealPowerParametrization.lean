import Mathlib
import sympy.Basic
import sympy.functions.special.RealPowerParametrization


/--
[RealPowerParametrization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/RealPowerParametrization.lean)
-/
@[path]
private lemma exists_parametrization_of_rpow_eq_rpow_eq
-- given
  (x y : ℝ)
  (hy : 0 < y)
  (hyx : y < x)
  (hxy : Real.rpow x y = Real.rpow y x) :
-- imply
  ∃ (t : ℝ), 0 < t ∧
    (y = Real.rpow (1 + 1 / t) t ∧ x = Real.rpow (1 + 1 / t) (t + 1)) := by
-- proof
  apply MetaMathlibExt.exists_parametrization_of_rpow_eq_rpow x y hy hyx hxy


-- created on 2026-10-11
