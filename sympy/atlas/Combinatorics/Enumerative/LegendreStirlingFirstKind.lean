/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean -/

import sympy.atlas.Combinatorics.Enumerative.JacobiStirlingFirstKind
namespace MetaMathlibExt

/-- Generating polynomial for the Legendre-Stirling numbers of the first kind,
`∏ i ∈ Finset.range n, (X - i * (i + 1))` over `Polynomial ℤ`.
Concept `jis_sem_f66a64ccd0402d409b050315`, source equation `e:JacobiStirling1` /
`e:LeStirling` (statements `jis_01122ed9cc65cc42cecf4da1`,
`jis_073a5750ee8a25ebbba42d0c`). -/
noncomputable def legendreStirlingFirstPoly (n : ℕ) : Polynomial ℤ :=
  jacobiStirlingFirstPoly n (1 : ℤ)

/-- Legendre-Stirling number of the first kind `J(n, k; 1)`, defined as the
coefficient of `x ^ k` in the product over `i = 0, ..., n - 1` of
`(x - i * (i + 1))`.
Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
noncomputable def legendreStirlingFirst (n k : ℕ) : ℤ :=
  jacobiStirlingFirst n k (1 : ℤ)

/-- Initial row: `J(0, k; 1) = δ(0, k)`.
Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
theorem legendreStirlingFirst_zero (k : ℕ) :
    legendreStirlingFirst 0 k = if k = 0 then 1 else 0 := by
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_initial_row (R := ℤ) k (1 : ℤ)

/-- Triangular recurrence adjoining the next product factor:
`J(n + 1, k + 1; 1) = J(n, k; 1) - n * (n + 1) * J(n, k + 1; 1)`.
Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
theorem legendreStirlingFirst_succ (n k : ℕ) :
    legendreStirlingFirst (n + 1) (k + 1) =
      legendreStirlingFirst n k -
        (n : ℤ) * ((n + 1 : ℕ) : ℤ) * legendreStirlingFirst n (k + 1) := by
  simpa [legendreStirlingFirst, Nat.cast_add, Nat.cast_one] using
    jacobiStirlingFirst_recurrence (R := ℤ) n k (1 : ℤ)

/-- Support: `J(n, k; 1) = 0` for `k > n`.
Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
theorem legendreStirlingFirst_eq_zero_of_lt :
    ∀ (n k : ℕ), n < k → legendreStirlingFirst n k = 0 := by
  intro n k h
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_support (R := ℤ) n k (1 : ℤ) h

/-- Diagonal: `J(n, n; 1) = 1`.
Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
theorem legendreStirlingFirst_diag : ∀ (n : ℕ), legendreStirlingFirst n n = 1 := by
  intro n
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_diagonal (R := ℤ) n (1 : ℤ)

end MetaMathlibExt
