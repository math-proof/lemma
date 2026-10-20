/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralArithmeticalEulerianPolynomial.lean -/

import Mathlib.Algebra.Polynomial.Basic

/-!
# General arithmetical Eulerian polynomials

This file defines the general arithmetical Eulerian numbers and polynomials from Paul Barry,
*General Eulerian Polynomials as Moments Using Exponential Riordan Arrays*:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry4/barry271.tex>.
-/

namespace MetaMathlibExt

open scoped BigOperators

/-- The general arithmetical Eulerian number
`A_{n,k}(a,d) = ∑_{i=0}^k (-1)^i * C(n+1,i) * ((k+1-i)d-a)^n`. -/
def generalArithmeticalEulerianNumber (R : Type*) [Ring R] (n k : ℕ) (a d : R) : R :=
  ∑ i ∈ Finset.range (k + 1),
    (-1 : R) ^ i * (Nat.choose (n + 1) i : R) * ((k + 1 - i : ℕ) * d - a) ^ n

/-- The general arithmetical Eulerian polynomial
`P_n(t;a,d) = ∑_{k=0}^n A_{n,k}(a,d)t^k`. -/
noncomputable def generalArithmeticalEulerianPolynomial
    (R : Type*) [Ring R] (n : ℕ) (a d : R) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (generalArithmeticalEulerianNumber R n k a d) * Polynomial.X ^ k

end MetaMathlibExt
