import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.NormNum
/-!
# Bessel polynomials (classical definition)

Formalizes the classical n-th Bessel polynomial from the Schork source
(lines 285-288).
-/


namespace MetaMathlibExt

open scoped BigOperators

/-- The `n`-th classical Bessel polynomial `y_n` over the rationals:
`y_n(x) = ∑ k = 0 ^ n, ((n + k)! / (2 ^ k * k! * (n - k)!)) * x ^ k`. -/
noncomputable def besselPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((Nat.factorial (n + k) : ℚ) /
      ((2 ^ k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ))) *
      (Polynomial.X ^ k)

end MetaMathlibExt
