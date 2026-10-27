/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.RingTheory.PowerSeries.Polynomials.Part3
/-!
# Polynomials

This file formalizes the relationship between polynomials and formal power series (FPS),
following the treatment in the Algebraic Combinatorics book.

## Main Content

The key insight is that polynomials can be viewed as FPSs with only finitely many nonzero
coefficients. In Mathlib:
- `PowerSeries R` (notation: `R⟦X⟧`) is the type of formal power series
- `Polynomial R` (notation: `R[X]`) is the type of univariate polynomials
- `Polynomial.toPowerSeries` embeds polynomials into power series

## Main Definitions

* `FPS.IsPolynomial` - A predicate characterizing when a power series is a polynomial
  (i.e., has only finitely many nonzero coefficients)
* `FPS.polynomialSubalgebra` - The K-subalgebra of polynomial power series (Theorem 7.5.2)
* `FPS.polynomialSubring` - The subring of polynomial power series (Theorem 7.5.2)
* `FPS.polynomialSubmodule` - The K-submodule of polynomial power series (Theorem 7.5.2)
* `FPS.polyEval` - Polynomial evaluation at an element of a K-algebra (Definition 7.5.6)
* Notation `f⦃a⦄` for polynomial evaluation (corresponds to book notation `f[a]`)

## Main Results

* `FPS.isPolynomial_iff_finite_support` - A power series is a polynomial iff it has finite support
* `FPS.isPolynomial_add` - The sum of polynomials is a polynomial
* `FPS.isPolynomial_mul` - The product of polynomials is a polynomial
* `FPS.isPolynomial_neg` - The negation of a polynomial is a polynomial
* `FPS.isPolynomial_sub` - The difference of polynomials is a polynomial

## Evaluation/Substitution (def.pol.subs)

The evaluation of a polynomial `f` at an element `a` of a `K`-algebra `A` is denoted
`polyEval f a` or `f⦃a⦄`. This corresponds to Definition 7.5.6 (def.pol.subs) in the source:
  f[a] := Σ_{n ∈ ℕ} f_n · a^n

Key properties (Theorem 7.5.7, thm.pol.eval.a+b):
- `(f + g)⦃a⦄ = f⦃a⦄ + g⦃a⦄` : `eval_add'`
- `(f * g)⦃a⦄ = f⦃a⦄ * g⦃a⦄` : `eval_mul'`
- `(c • f)⦃a⦄ = c • f⦃a⦄` : `eval_smul'`
- `C(c)⦃a⦄ = algebraMap K A c` : `eval_C'`
- `X⦃a⦄ = a` : `eval_X'`
- `X^i⦃a⦄ = a^i` : `eval_X_pow'`
- `f⦃g⦃a⦄⦄ = (f.comp g)⦃a⦄` : `eval_comp'`

Special cases:
- `f⦃x⦄ = f` : `eval_X_eq_self`
- `f⦃0⦄ = f₀` : `eval_zero_eq_coeff_zero`
- `f⦃1⦄ = sum of coefficients` : `eval_one_eq_sum_coeffs`

## References

* Definition 7.5.1 (def.fps.pol) - Definition of polynomial as FPS with finite support ✓
* Theorem 7.5.2 (thm.fps.pol.ring) - K[x] is a subring of K[[x]] ✓
* Definition 7.5.3 (def.alg.ring) - Definition of (noncommutative) ring
* Definition 7.5.5 (def.alg.Kalg) - Definition of K-algebra
* Definition 7.5.6 (def.pol.subs) - Evaluation/substitution into polynomials ✓
* Theorem 7.5.7 (thm.pol.eval.a+b) - Properties of polynomial evaluation ✓

-/


namespace FPS

open Polynomial PowerSeries

variable {K : Type*} [CommRing K]

section RingExamples

-- Matrix rings are rings (noncommutative for n > 1)
example (n : ℕ) (R : Type*) [Ring R] [DecidableEq (Fin n)] : Ring (Matrix (Fin n) (Fin n) R) :=
  inferInstance

-- The quaternions over ℝ are a ring (noncommutative)
noncomputable example : Ring (Quaternion ℝ) := inferInstance

-- Endomorphism rings are rings
example (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Ring (Module.End R M) := inferInstance

-- Every commutative ring is a ring (commutativity is not required, just not forbidden)
example {K : Type*} [CommRing K] : Ring K := inferInstance

end RingExamples

/-! ## K-Algebras

### Definition 7.5.5 (def.alg.Kalg): K-Algebras

The source defines a K-algebra as a set A equipped with four maps:
- `⊕ : A × A → A` (addition)
- `⊖ : A × A → A` (subtraction)
- `⊙ : A × A → A` (multiplication)
- `⇀ : K × A → A` (scalar multiplication)

and two elements `0⃗ ∈ A` (zero) and `1⃗ ∈ A` (one), satisfying three properties:

1. **A is a (noncommutative) ring**: The set A with ⊕, ⊖, ⊙, 0⃗, 1⃗ is a ring
   (same as commutative ring but without commutativity of multiplication).

2. **A is a K-module**: The set A with ⊕, ⊖, ⇀, 0⃗ is a module.

3. **Compatibility property** (equation 7.5.2):
   `λ ⇀ (a ⊙ b) = (λ ⇀ a) ⊙ b = a ⊙ (λ ⇀ b)` for all `λ ∈ K` and `a, b ∈ A`.

In Mathlib, this is captured by the `Algebra` typeclass, which requires:
- `[Semiring A]` (or `[Ring A]` for rings with subtraction)
- `[Algebra K A]` which provides scalar multiplication and the compatibility property

The key property `λ(ab) = (λa)b = a(λb)` is expressed via:
- `Algebra.smul_mul_assoc`: `r • x * y = r • (x * y)`
- `Algebra.mul_smul_comm`: `x * r • y = r • (x * y)`
-/


section KAlgebra

variable {A : Type*} [Ring A] [Algebra K A]

/-! ### Property 1: A is a Ring

A K-algebra A is automatically a ring.
Note: The source allows noncommutative rings; in Mathlib, `Ring A` captures this.
For commutative algebras, we use `CommRing A`.
-/
/-! ### Property 2: A is a K-Module

A K-algebra A is automatically a K-module.
-/
/-! ### Property 3: Compatibility (Equation 7.5.2)

The key compatibility property: `λ(ab) = (λa)b = a(λb)` for all `λ ∈ K` and `a, b ∈ A`.

This says that scaling a product in A by a scalar λ ∈ K is equivalent to scaling
either of its two factors by λ.
-/

end KAlgebra

/-! ### Examples of K-Algebras

The source lists several examples of K-algebras:
- The ring K itself
- The ring K⟦X⟧ of formal power series
- The polynomial ring K[X] (as a subring of K⟦X⟧)
- The matrix ring K^{n×n} for each n ∈ ℕ
- Any quotient ring K/I where I is an ideal
- Any commutative ring containing K as a subring
-/


section KAlgebraExamples

/-- K is a K-algebra over itself.
    Label: def.alg.Kalg (Example 1) -/
example : Algebra K K := inferInstance

/-- The ring of formal power series K⟦X⟧ is a K-algebra.
    Label: def.alg.Kalg (Example 2) -/
noncomputable example : Algebra K (PowerSeries K) := inferInstance

/-- The polynomial ring K[X] is a K-algebra.
    Label: def.alg.Kalg (Example 3) -/
noncomputable example : Algebra K K[X] := inferInstance

/-- For any n, the matrix ring K^{n×n} is a K-algebra.
    Label: def.alg.Kalg (Example 4) -/
example (n : ℕ) : Algebra K (Matrix (Fin n) (Fin n) K) := inferInstance

/-- ℤ/m is a ℤ-algebra for any m.
    Label: def.alg.Kalg (Example 5) -/
example (m : ℕ) [NeZero m] : Algebra ℤ (ZMod m) := inferInstance

/-- ℚ is a ℤ-algebra.
    Label: def.alg.Kalg (Example 6) -/
example : Algebra ℤ ℚ := inferInstance

/-- Any ring is automatically a ℤ-algebra.
    This is because any ring has a unique ring homomorphism from ℤ.
    Label: def.alg.Kalg (Note) -/
example {R : Type*} [Ring R] : Algebra ℤ R := inferInstance

end KAlgebraExamples

/-! ### The algebraMap

In Mathlib, a K-algebra A comes with a ring homomorphism `algebraMap K A : K →+* A`
that embeds K into the center of A. This allows us to view elements of K as elements of A.
-/


section AlgebraMap

variable {A : Type*} [CommRing A] [Algebra K A]

/-- The algebraMap is a ring homomorphism from K to A.
    Label: def.alg.Kalg -/
example : K →+* A := algebraMap K A

end AlgebraMap
end FPS
