/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartialBellPolynomial.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Pi
open scoped BigOperators

/-!
# Partial Bell polynomials

The definition follows Miloud Mihoubi, *Some Congruences for the Partial Bell
Polynomials*, Journal of Integer Sequences 12 (2009), Article 09.4.1.
-/


namespace MetaMathlibExt

/-- The partial Bell polynomial `B_(n,k)` over a commutative semiring.

The vector `m` records multiplicities of blocks of sizes `1, ..., n+1`.
It is restricted by `∑ i * m_i = n` and `∑ m_i = k`; the source summand
is `n! * ∏ (x_i / i!)^m_i / m_i!`. Stable source identifier:
concept `jis_sem_a0ee8baeec8938655a1c8c9a`.
-/
def partialBellPolynomial {R : Type*} [CommSemiring R]
    (n k : ℕ) (x : ℕ → R) : R :=
  ∑ m ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Finset.range (n + 1)).filter
      (fun m => (∑ i, (i.val + 1) * m i = n) ∧ ∑ i, m i = k),
    (↑(n.factorial / ∏ i, (m i).factorial * (i.val + 1).factorial ^ m i) : R) *
      ∏ i, x (i.val + 1) ^ m i

end MetaMathlibExt
