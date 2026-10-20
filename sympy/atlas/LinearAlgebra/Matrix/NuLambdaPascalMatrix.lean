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

/-- Zero-extension clause `finite_support` of concept `jis_sem_48e0bb143520a73f6b828a27`
(source statement `jis_445c3486a9ca32dba0e8a333`): any entry with an index at
least `2 * n` is zero. -/
theorem IsNuLambdaPascalMatrix.finite_support (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
    (i j : ℕ) (hij : 2 * n ≤ i ∨ 2 * n ≤ j) : S i j = 0 :=
  h.1 i j hij

/-- Skew-symmetry clause `skew_symmetry` of concept `jis_sem_48e0bb143520a73f6b828a27`
(source statement `jis_445c3486a9ca32dba0e8a333`). -/
theorem IsNuLambdaPascalMatrix.skew (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
    (i j : ℕ) : S i j = -S j i :=
  h.2.1 i j

/-- Corner clause `corner` of concept `jis_sem_48e0bb143520a73f6b828a27`
(source statement `jis_445c3486a9ca32dba0e8a333`): the final superdiagonal entry
equals one. -/
theorem IsNuLambdaPascalMatrix.corner (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn) :
    S (2 * n - 2) (2 * n - 1) = 1 :=
  h.2.2.1

/-- Last-column clause `last_column` of concept `jis_sem_48e0bb143520a73f6b828a27`
(source statement `jis_445c3486a9ca32dba0e8a333`): each entry above the corner in
the last column is a `beta`-weighted sum of lower entries. -/
theorem IsNuLambdaPascalMatrix.last_column (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
    (j : ℕ) (hj : j < 2 * n - 2) :
    S j (2 * n - 1) = ∑ t : Fin N, beta t * S (j + t.val + 1) (2 * n - 1) :=
  h.2.2.2.1 j hj

/-- Interior clause `interior` of concept `jis_sem_48e0bb143520a73f6b828a27`
(source statement `jis_445c3486a9ca32dba0e8a333`): the two-parameter recurrence
involving `lam` and `nu`. -/
theorem IsNuLambdaPascalMatrix.interior (N n : ℕ) (nu lam : ℂ)
    (beta : Fin N → ℂ) (S : ℕ → ℕ → ℂ) (hn : 0 < n)
    (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
    (i j : ℕ) (hi : i < 2 * n - 1) (hj : j < 2 * n - 1) :
    S i j = lam * S (i + 1) (j + 1) + nu * (S (i + 1) j + S i (j + 1)) :=
  h.2.2.2.2 i j hi hj

end MetaMathlibExt
