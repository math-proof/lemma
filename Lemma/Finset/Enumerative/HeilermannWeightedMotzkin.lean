import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.HeilermannWeightedMotzkin
open MetaMathlibExt


/--
[exists_weightedMotzkin_coefficients_of_hasJacobiFraction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/HeilermannWeightedMotzkin.lean)
-/
@[path]
private lemma exists_weightedMotzkin_coefficients_of_hasJacobiFraction_eq
  [Ring K]
  {a alpha beta : ℕ → K}
  {mu0 : K}
  {F : ℕ → PowerSeries K}
-- given
  (h : HasJacobiFraction a alpha beta mu0 F) :
-- imply
  ∃ M : ℕ → ℕ → K, M 0 0 = 1 ∧
    (∀ j, M 0 (j + 1) = 0) ∧
    (∀ n, M (n + 1) 0 = alpha 0 * M n 0 + beta 1 * M n 1) ∧
    (∀ n j, M (n + 1) (j + 1) =
    M n j + alpha (j + 1) * M n (j + 1) +
    beta (j + 2) * M n (j + 2)) ∧
    ∀ n, a n = mu0 * M n 0 := by
-- proof
  apply MetaMathlibExt.exists_weightedMotzkin_coefficients_of_hasJacobiFraction h


-- created on 2026-10-20
