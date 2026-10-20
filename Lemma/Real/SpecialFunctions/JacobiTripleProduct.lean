import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.JacobiTripleProduct
open MathlibExt
open BigOperators
open scoped BigOperators
open MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct


/--
[jacobi_triple_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/JacobiTripleProduct.lean)
-/
@[path]
private lemma jacobi_triple_product_eq
  {z q : ℂ}
-- given
  (hz : z ≠ 0)
  (hq : ‖q‖ < 1) :
-- imply
  Summable (fun n : ℤ => z ^ n * q ^ (n * n).toNat) ∧
    Multipliable (fun n : ℕ =>
    (1 - q ^ (2 * n + 2)) * (1 + z * q ^ (2 * n + 1)) *
    (1 + z⁻¹ * q ^ (2 * n + 1))) ∧
    (∑' n : ℤ, z ^ n * q ^ (n * n).toNat) =
    ∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + z * q ^ (2 * n + 1)) *
    (1 + z⁻¹ * q ^ (2 * n + 1)) := by
-- proof
  apply MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product z q hz hq


-- created on 2026-10-20
