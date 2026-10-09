import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.BesselPolynomial

open MetaMathlibExt
open scoped BigOperators

/--
[besselPolynomial_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/BesselPolynomial.lean)
-/
@[path]
private lemma besselPolynomial_eq_sum_eq
-- given
  (n : ℕ) :
-- imply
  besselPolynomial n =
    ∑ k ∈ Finset.range (n + 1),
      Polynomial.C ((Nat.factorial (n + k) : ℚ) /
        ((2 ^ k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ))) *
        (Polynomial.X ^ k) := by
-- proof
  apply besselPolynomial_eq_sum


/--
[besselPolynomial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/BesselPolynomial.lean)
-/
@[path]
private lemma besselPolynomial_zero_eq :
-- imply
  besselPolynomial 0 = 1 := by
-- proof
  apply besselPolynomial_zero


/--
[besselPolynomial_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/BesselPolynomial.lean)
-/
@[path]
private lemma besselPolynomial_one_eq :
-- imply
  besselPolynomial 1 = Polynomial.C 1 + Polynomial.X := by
-- proof
  apply besselPolynomial_one


/--
[besselPolynomial_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/BesselPolynomial.lean)
-/
@[path]
private lemma besselPolynomial_two_eq :
-- imply
  besselPolynomial 2 =
    Polynomial.C 1 + Polynomial.C 3 * Polynomial.X +
      Polynomial.C 3 * (Polynomial.X ^ 2) := by
-- proof
  apply besselPolynomial_two


-- created on 2026-10-09
