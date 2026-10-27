/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.RingTheory.PowerSeries.Polynomials.Part3
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

section Evaluation

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Evaluation of a polynomial at an element of a K-algebra.
This is Definition 7.5.6 (def.pol.subs).

Given a polynomial f ∈ K[X] and an element a of a K-algebra A,
we define f[a] := Σ_{n ∈ ℕ} f_n · a^n.

The sum is essentially finite since f is a polynomial (only finitely many
coefficients are nonzero).

In Mathlib, this is implemented as `Polynomial.aeval a f`. -/
noncomputable abbrev polyEval (f : K[X]) (a : A) : A := aeval a f

end Evaluation
end FPS
