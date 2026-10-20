import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
open scoped BigOperators
open MetaMathlibExt


/--
[hankelTransform_eq_prod_of_weightedMotzkin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/HeilermannWeightedMotzkinDeterminant.lean)
-/
@[path]
private lemma hankelTransform_eq_prod_of_weightedMotzkin_eq
  [CommRing K]
  {alpha beta : ℕ → K}
  {M : ℕ → ℕ → K}
  {mu0 : K}
  {n : ℕ}
-- given
  (hzero : M 0 0 = mu0)
  (hzero_succ : ∀ j : ℕ, M 0 (j + 1) = 0)
  (hbase : ∀ n : ℕ, M (n + 1) 0 = alpha 0 * M n 0 + beta 1 * M n 1)
  (hstep : ∀ n j : ℕ, M (n + 1) (j + 1) = M n j + alpha (j + 1) * M n (j + 1) + beta (j + 2) * M n (j + 2)) :
-- imply
  hankelTransform (fun m => M m 0) n =
    mu0 ^ (n + 1) * ∏ j ∈ Finset.range n, beta (j + 1) ^ (n - j) := by
-- proof
  apply MetaMathlibExt.hankelTransform_eq_prod_of_weightedMotzkin hzero hzero_succ hbase hstep n


-- created on 2026-10-20
