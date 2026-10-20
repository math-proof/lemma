import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.AndrewsJacobiTripleProduct
open MetaMathlibExt


/--
[andrews_jacobi_triple_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/AndrewsJacobiTripleProduct.lean)
-/
@[path]
private lemma andrews_jacobi_triple_product_eq
  {q : ℂ}
  {k i : ℕ}
-- given
  (hi_pos : 0 < i)
  (hi_le : i ≤ k)
  (hq : ‖q‖ < 1) :
-- imply
  ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n) =
    ∏' n : ℕ, (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
    (1 - q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
    (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ))) := by
-- proof
  apply MetaMathlibExt.andrews_jacobi_triple_product q k i hi_pos hi_le hq

/--
[andrews_jacobi_triple_product_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/AndrewsJacobiTripleProduct.lean)
-/
@[path]
private lemma andrews_jacobi_triple_product_summable_eq
  {q : ℂ}
  {k i : ℕ}
-- given
  (hi_le : i ≤ k)
  (hq : ‖q‖ < 1) :
-- imply
  Summable (fun n : ℤ => (-1 : ℂ) ^ n *
    q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (i : ℤ) * n)) := by
-- proof
  apply MetaMathlibExt.andrews_jacobi_triple_product_summable q k i hi_le hq

/--
[andrews_jacobi_triple_product_multipliable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/AndrewsJacobiTripleProduct.lean)
-/
@[path]
private lemma andrews_jacobi_triple_product_multipliable_eq
  {q : ℂ}
  {k i : ℕ}
-- given
  (hi_pos : 0 < i)
  (hi_le : i ≤ k)
  (hq : ‖q‖ < 1) :
-- imply
  Multipliable (fun n : ℕ => (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1))) *
    (1 - q ^ ((2 * (k : ℤ) + 1) * (n : ℤ) + (i : ℤ))) *
    (1 - q ^ ((2 * (k : ℤ) + 1) * ((n : ℤ) + 1) - (i : ℤ)))) := by
-- proof
  apply MetaMathlibExt.andrews_jacobi_triple_product_multipliable q k i hi_pos hi_le hq


-- created on 2026-10-20
