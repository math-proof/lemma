/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/OrdinaryRiordanPascalLikeMatrix.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Ordinary Riordan Pascal-like matrix

Provenance: concept `jis_sem_d14a1d74e61f27c561413829`; source statements
`jis_55826aed9bbc43db2e540fc8`, `jis_a1500757725c00536c86ba35`,
`jis_ac99ac2ae8aedbaafe1c53e3`.
-/


namespace MetaMathlibExt

/-- Ordinary Riordan Pascal-like matrix entry `T(n, k; r)` (concept
`jis_sem_d14a1d74e61f27c561413829`; statements `jis_55826aed9bbc43db2e540fc8`,
`jis_a1500757725c00536c86ba35`, `jis_ac99ac2ae8aedbaafe1c53e3`).

This is the entry formula for the ordinary Riordan array
`(1 / (1 - x), x * (1 + r * x) / (1 - x))`, denoted `T(r)`, with integer
parameter `r`. The second binomial factor is written `choose (n - j) k` by
binomial symmetry, so terms with `j > n - k` vanish rather than being
corrupted by truncated subtraction. Source specializations: `r = 0` gives
Pascal's triangle and `r = 1` gives the Delannoy triangle. -/
def ordinaryRiordanPascalLikeMatrix (n k : ℕ) (r : ℤ) : ℤ :=
  Finset.sum (Finset.range (k + 1)) fun j =>
    (k.choose j : ℤ) * ((n - j).choose k : ℤ) * r ^ j

end MetaMathlibExt
