/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerSeidelMatrix.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Data.Nat.Choose.Basic
/-!
# Euler–Seidel matrices

Source: Ayhan Dil and István Mező, *A Symmetric Algorithm for Hyperharmonic and Fibonacci Numbers*:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.tex>.
-/


namespace MetaMathlibExt

/-- Euler-Seidel matrix of an initial sequence (concept `jis_sem_2d9f269b63b4ba3ecb7264dc`,
required clause `jis_a4c0543f8c36d23dbc01b6aa`): given `a : ℕ → M`, the array `a_n^k`
with `a_n^0 = a_n` for `n ≥ 0` and `a_n^k = a_n^{k-1} + a_{n+1}^{k-1}` for `n ≥ 0`,
`k ≥ 1`. -/
def eulerSeidelMatrix {M : Type*} [Add M] (a : ℕ → M) : ℕ → ℕ → M
  | n, 0 => a n
  | n, k + 1 => eulerSeidelMatrix a n k + eulerSeidelMatrix a (n + 1) k

end MetaMathlibExt
