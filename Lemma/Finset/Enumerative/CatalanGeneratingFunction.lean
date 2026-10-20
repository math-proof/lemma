import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CatalanGeneratingFunction
open scoped Topology
open MetaMathlibExt.CatalanGeneratingFunction


/--
[catalan_generating_function_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
private lemma catalan_generating_function_sqrt_eq
  {x : ℝ}
-- given
  (hx : |x| < 1 / 4)
  (hx0 : x ≠ 0) :
-- imply
  ∑' n : ℕ, (catalan n : ℝ) * x ^ n =
    (1 - Real.sqrt (1 - 4 * x)) / (2 * x) := by
-- proof
  apply MetaMathlibExt.CatalanGeneratingFunction.catalan_generating_function_sqrt x hx hx0


-- created on 2026-10-20
