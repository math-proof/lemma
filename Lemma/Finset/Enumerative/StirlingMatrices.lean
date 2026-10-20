import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.StirlingMatrices
open BigOperators
open MetaMathlibExt


/--
[sum_signedStirlingFirst_mul_stirlingSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma sum_signedStirlingFirst_mul_stirlingSecond_eq
  {n m : ℕ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k * (Nat.stirlingSecond k m : ℤ) =
    if n = m then 1 else 0 := by
-- proof
  apply MetaMathlibExt.sum_signedStirlingFirst_mul_stirlingSecond n m

/--
[stirlingMatrices_mutualInverse_and_lowerTriangular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma stirlingMatrices_mutualInverse_and_lowerTriangular_eq
  {N : ℕ} :
-- imply
  let s : Matrix (Fin N) (Fin N) ℤ := by
-- proof
  apply MetaMathlibExt.stirlingMatrices_mutualInverse_and_lowerTriangular N


-- created on 2026-10-20
