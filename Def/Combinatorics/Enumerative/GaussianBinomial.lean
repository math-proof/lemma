/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianBinomial.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Ring
/-!
# Gaussian binomial coefficients and finite q-Pochhammer symbols

Shared finite q-series layer: the Gaussian binomial coefficient `gaussBinom`,
defined by the Pascal recursion in `M`, the finite q-Pochhammer symbol
`qPochFin`, and the product formula relating them.
-/


section

namespace MathlibExt

/-- Gaussian binomial coefficient `G_Q(M, k)`: `G(M, 0) = 1`, `G(0, k+1) = 0`,
and `G(M+1, k+1) = G(M, k) + Q^(k+1) * G(M, k+1)`. -/
def gaussBinom {R : Type*} [Semiring R] (Q : R) (M : ℕ) : ℕ → R
  | 0 => 1
  | k + 1 =>
      match M with
      | 0 => 0
      | M + 1 => gaussBinom Q M k + Q ^ (k + 1) * gaussBinom Q M (k + 1)

/-- Finite q-Pochhammer symbol `P_Q(m) = ∏_{i < m} (1 - Q^(i+1))`. -/
def qPochFin {R : Type*} [CommRing R] (Q : R) (m : ℕ) : R :=
  ∏ i ∈ Finset.range m, (1 - Q ^ (i + 1))

end MathlibExt
end
