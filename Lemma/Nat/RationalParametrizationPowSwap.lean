import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RationalParametrizationPowSwap
open MetaMathlibExt


/--
[rational_parametrization_pow_swap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RationalParametrizationPowSwap.lean)
-/
@[path]
private lemma rational_parametrization_pow_swap_eq
  {x y : ℚ}
-- given
  (hx : 0 < x)
  (hy : 0 < y)
  (hyx : y < x)
  (h : (x : ℝ) ^ (y : ℝ) = (y : ℝ) ^ (x : ℝ)) :
-- imply
  ∃ v : ℕ, 0 < v ∧
    x = (1 + 1 / (v : ℚ)) ^ (v + 1) ∧ y = (1 + 1 / (v : ℚ)) ^ v := by
-- proof
  apply MetaMathlibExt.rational_parametrization_pow_swap x y hx hy hyx h


-- created on 2026-10-20
