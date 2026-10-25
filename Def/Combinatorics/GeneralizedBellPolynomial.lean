/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/GeneralizedBellPolynomial.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Ring.Defs
open scoped BigOperators


namespace MetaMathlibExt

/-! Generalized Stirling numbers `𝔖_{s;h}(n, k)` from JIS VOL15/Schork,
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex>, lines 154–160,
SHA-256 `f3006b7ef496c012bfca9644eaec996857fb2b465fcb0f7de1a9807e3eb1d659`.

Concept `jis_term_0fc9852339ef66823c96d1ac` (semantic concept
`jis_sem_bc9000de6649aba0f779d229`). The source recurrence is
`𝔖_{s;h}(n+1,k) = 𝔖_{s;h}(n,k-1) + h * (k + s * (n-k)) * 𝔖_{s;h}(n,k)`.

In the Lean pattern `(n + 1, k + 1)`, source `k` is `k + 1`, so the factor is
`h * ((k + 1) + s * (n - (k + 1)))`. Above-diagonal terms remain zero, so
truncated natural-number subtraction does not alter those values. -/
def genStirling {R : Type*} [CommRing R] (s h : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
    genStirling s h n k +
      h * ((↑(k + 1) : R) + s * (↑(n - (k + 1)) : R)) *
        genStirling s h n (k + 1)

/-- The generalized Bell number `𝔅_{s;h}(n) = ∑ k, 𝔖_{s;h}(n,k)`. -/
def genBellNumber {R : Type*} [CommRing R] (s h : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), genStirling s h n k

/-- The generalized Bell polynomial
`𝔅_{s;h|n}(x) = ∑ k, 𝔖_{s;h}(n,k) x^k`. -/
def genBellPolynomial {R : Type*} [CommRing R] (s h : R) (n : ℕ) (x : R) : R :=
  ∑ k ∈ Finset.range (n + 1), genStirling s h n k * x ^ k

end MetaMathlibExt
