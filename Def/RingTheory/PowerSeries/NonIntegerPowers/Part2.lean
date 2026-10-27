/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.ExpLog.Part6
import Notation.RingTheory.PowerSeries.NonIntegerPowers
open scoped Polynomial PowerSeries
open PowerSeries Finset

/-!
# Non-integer Powers of Formal Power Series

This file formalizes non-integer powers of formal power series (FPS) and the generalized
Newton binomial formula, following Section 7.12 (sec.gf.nips) of the source.

## Main Definitions

* `AlgebraicCombinatorics.FPS.fpsPow`: The c-th power f^c for f ∈ K⟦X⟧₁ (FPS with constant term 1) and c ∈ K,
  defined as `Exp(c * Log f)` (Definition def.fps.power-c).

## Main Results

* `AlgebraicCombinatorics.FPS.fpsPow_add`: The rule f^{a+b} = f^a * f^b (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.fpsPow_mul`: The rule (fg)^a = f^a * g^a (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.fpsPow_pow`: The rule (f^a)^b = f^{ab} (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.generalizedNewtonBinomial`: The generalized Newton binomial formula
  (1+x)^c = ∑_{k ∈ ℕ} C(c,k) x^k (Theorem thm.fps.gen-newton).
* `AlgebraicCombinatorics.FPS.binomialIdentity`: The binomial identity
  ∑_{i=0}^k C(n+i-1,i) C(n,k-2i) = C(n+k-1,k) (Proposition prop.binom.nCk-2i-qedmo.CN).

## Implementation Notes

The definition of f^c uses the Exp and Log maps from Mathlib. Specifically:
- For f ∈ K⟦X⟧₁ (constant term 1), we define f^c := Exp(c * Log f)
- This requires K to be a commutative ℚ-algebra

The generalized Newton binomial formula is proved using the polynomial identity trick:
both sides are polynomials in c that agree on ℕ, hence they agree everywhere.

## References

* Source: NonIntegerPowers.tex, Section sec.gf.nips
-/


namespace AlgebraicCombinatorics

namespace FPS

variable {K : Type*} [CommRing K] [Algebra ℚ K]

variable [BinomialRing K]

variable [CharZero K]

/-- logSeries over ℚ. This is the base version that maps to logSeries K under algebraMap. -/
noncomputable def logSeriesQ : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else ((-1 : ℚ)^(n-1) / n)

/-- The polynomial for Ring.choose: Q_k(X) = (1/k!) * descPochhammer(X, k) over ℚ.
    This polynomial, when mapped to K and evaluated at c, gives Ring.choose c k. -/
noncomputable def choosePoly (k : ℕ) : Polynomial ℚ :=
  (k.factorial : ℚ)⁻¹ • (descPochhammer ℚ k)

/-- The polynomial for coeff k (fpsPow (1+X) c).
    This is ∑_{d=0}^k (coeff d exp • coeff k (logSeriesQ^d)) • X^d.
    When evaluated at c, this gives coeff k (fpsExp (c • logSeries)). -/
noncomputable def coeffExpPoly (k : ℕ) : Polynomial ℚ :=
  ∑ d ∈ Finset.range (k + 1),
    Polynomial.C (coeff d (exp ℚ) * coeff k (logSeriesQ^d)) * Polynomial.X^d

/-!
## Application: The Catalan Number Generating Function

The equation C = 1 + xC² for the Catalan generating function has solution
C = (1 - √(1-4x))/(2x) = (1 - (1-4x)^{1/2})/(2x)

This is now rigorous using our definition of non-integer powers.
-/


/-- The square root of 1-4x as an FPS.
    √(1-4x) = (1-4x)^{1/2} = (1 + (-4x))^{1/2}
    Label: eq.sec.gf.exas.2.(1+x)1/2 -/
noncomputable def sqrtOneMinusFourX : ℚ⟦X⟧ :=
  (1 + (-4 : ℚ) • X) ^ᶠ (1/2 : ℚ)

/-!
## Another Application: A Binomial Identity (Proposition prop.binom.nCk-2i-qedmo.CN)

For n ∈ ℂ and k ∈ ℕ:
∑_{i=0}^k C(n+i-1, i) C(n, k-2i) = C(n+k-1, k)

The proof uses generating functions:
- Define f = ∑_{i ∈ ℕ} C(n+i-1, i) x^{2i} = (1-x²)^{-n}
- Define g = ∑_{j ∈ ℕ} C(n, j) x^j = (1+x)^n
- Then fg = (1-x)^{-n} = ∑_{i ∈ ℕ} C(n+i-1, i) x^i
- Comparing coefficients of x^k gives the identity
-/
/-!
### Helper Lemmas for the Binomial Identity

We prove the identity using generating functions:
- Define f = ∑_{i ∈ ℕ} C(n+i-1, i) x^{2i}
- Define g = ∑_{j ∈ ℕ} C(n, j) x^j = (1+x)^n
- Show that fg = (1-x)^{-n} using the factorization (1-x²) = (1-x)(1+x)
- Compare coefficients of x^k
-/

/-- The series f = ∑_i C(n+i-1, i) x^{2i} used in the proof -/
noncomputable def f_series' (n : K) : K⟦X⟧ :=
  mk fun m => if Even m then Ring.choose (n + ((m/2 : ℕ) : K) - 1) (m/2) else 0

/-- The series g = (1+x)^n = binomialSeries K n -/
noncomputable def g_series' (n : K) : K⟦X⟧ := binomialSeries K n

/-!
### Infrastructure for the Polynomial Identity Principle

The following lemmas establish the connection between binomialSeries and invOneSubPow,
which is needed for proving the coefficient identity using the polynomial identity principle.
-/
/-!
## Consistency with Integer Powers

Our definition of f^c agrees with the standard definition when c is a natural number.
-/
/-!
## The Proof Method: Polynomial Identity Trick

The proof of the generalized Newton formula uses the "polynomial identity trick":
If two polynomials (with rational coefficients) agree on all natural numbers,
they must be equal as polynomials, and hence agree on all values in any ℚ-algebra.

This is formalized in Mathlib as polynomial equality from infinitely many roots.
-/

end FPS
end AlgebraicCombinatorics
