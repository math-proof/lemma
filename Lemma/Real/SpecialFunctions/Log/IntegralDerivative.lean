import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.Log.IntegralDerivative
open scoped Topology
open Real


/--
[logarithmicIntegralReal_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/IntegralDerivative.lean)
-/
@[path]
private lemma logarithmicIntegralReal_zero_eq
  :
-- imply
  logarithmicIntegralReal 0 = 0 := by
-- proof
  apply Real.logarithmicIntegralReal_zero

/--
[logarithmicIntegralReal_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/IntegralDerivative.lean)
-/
@[path]
private lemma logarithmicIntegralReal_of_mem_eq
  {x : ℝ}
-- given
  (h : 0 ≤ x ∧ x ≠ 1) :
-- imply
  logarithmicIntegralReal x =
    Real.logarithmicIntegral (⟨x, h⟩ : Real.LogarithmicIntegralDomain) := by
-- proof
  apply Real.logarithmicIntegralReal_of_mem h

/--
[logarithmicIntegralReal_of_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/IntegralDerivative.lean)
-/
@[path]
private lemma logarithmicIntegralReal_of_lt_one_eq
  {x : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hx1 : x < 1) :
-- imply
  logarithmicIntegralReal x = ∫ t in (0 : ℝ)..x, (Real.log t)⁻¹ := by
-- proof
  apply Real.logarithmicIntegralReal_of_lt_one hx0 hx1

/--
[logarithmicIntegralReal_of_one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/IntegralDerivative.lean)
-/
@[path]
private lemma logarithmicIntegralReal_of_one_lt_eq
  {x : ℝ}
-- given
  (hx : 1 < x) :
-- imply
  logarithmicIntegralReal x =
    (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
    ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ := by
-- proof
  apply Real.logarithmicIntegralReal_of_one_lt hx

/--
[hasDerivAt_logarithmicIntegralReal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/IntegralDerivative.lean)
-/
@[path]
private lemma hasDerivAt_logarithmicIntegralReal_eq
  {x : ℝ}
-- given
  (hx_pos : 0 < x)
  (hx_ne_one : x ≠ 1) :
-- imply
  HasDerivAt logarithmicIntegralReal (1 / Real.log x) x := by
-- proof
  apply Real.hasDerivAt_logarithmicIntegralReal hx_pos hx_ne_one


-- created on 2026-10-20
