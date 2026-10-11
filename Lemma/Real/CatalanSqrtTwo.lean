import Mathlib
import sympy.Basic
import sympy.functions.special.CatalanSqrtTwo


/--
[CatalanSqrtTwo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/CatalanSqrtTwo.lean)
-/
@[path]
private lemma catalan_has_prod_sqrt_two_is :
-- imply
  HasProd (fun m : ℕ =>
    (((4 * m + 2 : ℕ) : ℝ) ^ 2) /
      (((4 * m + 1 : ℕ) : ℝ) * ((4 * m + 3 : ℕ) : ℝ)))
    (Real.sqrt 2) := by
-- proof
  apply SpecialFunctions.CatalanSqrtTwo.catalan_hasProd_sqrt_two


-- created on 2026-10-11
