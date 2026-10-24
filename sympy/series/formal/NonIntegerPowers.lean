/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.series.formal.ExpLog
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


open scoped Polynomial PowerSeries
open PowerSeries Finset

namespace AlgebraicCombinatorics

namespace FPS

variable {K : Type*} [CommRing K] [Algebra ℚ K]
/-!
## The Exp and Log Maps

We use Mathlib's `PowerSeries.exp` for the exponential series.
For the logarithm, we define it via the standard series log(1+x) = ∑_{n≥1} (-1)^{n-1}/n * x^n.
-/


/-- The logarithm series: log(1+x) = x - x²/2 + x³/3 - x⁴/4 + ...
    This is `\overline{log}` in the source notation.
    Label: def.fps.logbar -/
noncomputable def logSeries : K⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ)^(n-1) / n)
/-!
## FPS with Constant Term 1

We define the set K⟦X⟧₁ of FPS with constant term 1.
This is the domain on which non-integer powers are defined.
-/


/-- An FPS has constant term 1.
    This is the condition for f ∈ K⟦X⟧₁ in the source.
    Label: def.fps.Exp-Log-maps (b)

    Note: This is definitionally equivalent to membership in `PowerSeries₁` from ExpLog.lean:
    `HasConstantTermOne f ↔ f ∈ PowerSeries₁`. The `Prop` form is used here for convenience
    in hypotheses, while `PowerSeries₁` (a `Set`) is used in ExpLog.lean for subgroup structures. -/
def HasConstantTermOne (f : K⟦X⟧) : Prop := constantCoeff f = 1

section HasConstantTermOneBasic
variable {R : Type*} [CommRing R]

end HasConstantTermOneBasic
/-!
## The Log Map for FPS with Constant Term 1

For f ∈ K⟦X⟧₁, we define Log(f) by substituting (f-1) into the log series.
Since f has constant term 1, f-1 has constant term 0, so the substitution is well-defined.
-/


/-- The Log map: Log(f) = log_series(f-1) = logSeries.subst (f-1)
    This is well-defined when f has constant term 1.
    Label: def.fps.Exp-Log-maps -/
noncomputable def fpsLog (f : K⟦X⟧) : K⟦X⟧ :=
  (logSeries (K := K)).subst (f - 1)
/-!
## The Exp Map for FPS with Constant Term 0

For g ∈ K⟦X⟧₀ (constant term 0), we define Exp(g) by substituting g into exp.
-/


/-- The Exp map: Exp(g) = exp(g) = (exp K).subst g
    This is well-defined when g has constant term 0.
    Label: def.fps.Exp-Log-maps -/
noncomputable def fpsExp (g : K⟦X⟧) : K⟦X⟧ :=
  (exp K).subst g
/-!
## Definition of Non-integer Powers (Definition def.fps.power-c)

For f ∈ K⟦X⟧₁ and c ∈ K, we define f^c := Exp(c * Log(f)).

This definition:
- Does not conflict with integer powers (since Log and Exp are inverses on the appropriate domains)
- Makes the rules of exponents hold
- Yields (1+x)^c = ∑ C(c,k) x^k (generalized Newton binomial formula)
-/


/-- The c-th power of an FPS f with constant term 1.
    f^c := Exp(c * Log(f)) = exp.subst (c * log_series.subst (f-1))
    Label: def.fps.power-c -/
noncomputable def fpsPow (f : K⟦X⟧) (c : K) : K⟦X⟧ :=
  fpsExp (c • fpsLog f)

/-- Notation for non-integer powers (when needed) -/
scoped notation:80 f " ^ᶠ " c:81 => fpsPow f c
/-!
## Rules of Exponents (Theorem thm.fps.power-c.rules)

For any a, b ∈ K and f, g ∈ K⟦X⟧₁:
- f^{a+b} = f^a * f^b
- (fg)^a = f^a * g^a
- (f^a)^b = f^{ab}
-/
/-!
### Connection to ExpLog.lean

We establish the connection between our `logSeries`/`fpsLog`/`fpsExp` definitions
and the `logbar`/`Log`/`Exp` definitions from ExpLog.lean. This allows us to use
the `Exp_Log` theorem to prove `fpsPow_one`.
-/
/-!
## Generalized Newton Binomial Formula (Theorem thm.fps.gen-newton)

For any c ∈ K (where K is a commutative ℚ-algebra):
(1+x)^c = ∑_{k ∈ ℕ} C(c,k) x^k

where C(c,k) = c(c-1)(c-2)⋯(c-k+1)/k! is the generalized binomial coefficient.

Note: We need K to be a BinomialRing to use Ring.choose. Since K is a ℚ-algebra,
it has a BinomialRing structure.
-/


variable [BinomialRing K]
/-!
### Key lemmas for the proof

The proof strategy is:
1. Show that `fpsLog (1+X) = logSeries`
2. Show that `fpsPow (1+X) c = fpsExp (c • logSeries)`
3. Show that for natural `n`, `fpsExp (n • logSeries) = (1+X)^n` using the exp functional equation
4. Use `binomialSeries_nat`: `binomialSeries K n = (1+X)^n`
5. Apply the polynomial identity trick: both sides have polynomial coefficients in `c`
   that agree on all natural numbers, hence they agree everywhere
-/
/-!
### Helper lemmas for the polynomial identity principle

The proof of `generalizedNewtonBinomial` uses the polynomial identity principle:
both `Ring.choose c k` and `coeff k ((1+X)^ᶠ c)` are polynomial functions of `c`
that agree on all natural numbers, hence they are equal.

The following lemmas establish the polynomial structure of `Ring.choose c k`.
-/


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
