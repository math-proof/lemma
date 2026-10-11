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

/-- Restatement of the defining formula for `besselPolynomial`. -/
theorem besselPolynomial_eq_sum (n : ℕ) :
    besselPolynomial n =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C ((Nat.factorial (n + k) : ℚ) /
          ((2 ^ k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ))) *
          (Polynomial.X ^ k) :=
  rfl

/-- The value `y_0 = 1`. -/
theorem besselPolynomial_zero : besselPolynomial 0 = 1 := by
  unfold besselPolynomial
  norm_num [Finset.sum_range_one]

/-- The value `y_1 = 1 + X`. -/
theorem besselPolynomial_one :
    besselPolynomial 1 = Polynomial.C 1 + Polynomial.X := by
  unfold besselPolynomial
  norm_num [Finset.sum_range_succ, Finset.sum_range_one]

/-- The value `y_2 = 1 + 3 * X + 3 * X ^ 2`. -/
theorem besselPolynomial_two :
    besselPolynomial 2 =
      Polynomial.C 1 + Polynomial.C 3 * Polynomial.X +
        Polynomial.C 3 * (Polynomial.X ^ 2) := by
  unfold besselPolynomial
  simp only [Finset.sum_range_succ]
  norm_num [Nat.factorial]

end MetaMathlibExt
