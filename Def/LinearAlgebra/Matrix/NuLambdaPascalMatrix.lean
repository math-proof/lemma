/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean -/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
/-!
# Nu,lambda-Pascal matrix with coefficients

Production formalization of the source definition (concept
`jis_sem_48e0bb143520a73f6b828a27`, source statement
`jis_445c3486a9ca32dba0e8a333`) using zero-based indexing.
-/


namespace MetaMathlibExt

open scoped BigOperators

/-- Nu,lambda-Pascal matrix with coefficients (concept `jis_sem_48e0bb143520a73f6b828a27`,
source statement `jis_445c3486a9ca32dba0e8a333`): zero-extended `2n × 2n`
skew-symmetric matrix over `ℂ` given by the corner value, the last-column sum,
and the interior recurrence. The unused binder `_hn : 0 < n` records the source
hypothesis `n > 0` licensing the zero-based positions `2 * n - 2` and
`2 * n - 1`.

The API deliberately also permits `N = 0`; then the beta-index is empty and
the last-column sum is zero. The source's intended coefficient families have
`N > 0`. -/
def IsNuLambdaPascalMatrix (N n : ℕ) (nu lam : ℂ) (beta : Fin N → ℂ)
    (S : ℕ → ℕ → ℂ) (_hn : 0 < n) : Prop :=
  (∀ i j, 2 * n ≤ i ∨ 2 * n ≤ j → S i j = 0) ∧
  (∀ i j, S i j = -S j i) ∧
  (S (2 * n - 2) (2 * n - 1) = 1) ∧
  (∀ j, j < 2 * n - 2 →
    S j (2 * n - 1) = ∑ t : Fin N, beta t * S (j + t.val + 1) (2 * n - 1)) ∧
  (∀ i j, i < 2 * n - 1 → j < 2 * n - 1 →
    S i j = lam * S (i + 1) (j + 1) + nu * (S (i + 1) j + S i (j + 1)))

end MetaMathlibExt
