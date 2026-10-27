/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.RingTheory.PowerSeries.Polynomials.Part2
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

/-! ## K[x] as a Subalgebra of K[[x]]

Theorem 7.5.2 (thm.fps.pol.ring): The set K[x] is a subring of K[[x]] (closed under addition,
subtraction, and multiplication, and contains 0 and 1) and a K-submodule of K[[x]] (closed
under addition and scalar multiplication).

These two properties together mean that K[x] forms a K-subalgebra of K[[x]].
-/


/-- The set of polynomial power series forms a K-subalgebra of K[[x]].
This is Theorem 7.5.2 (thm.fps.pol.ring) in the source:
K[x] is a subring of K[[x]] (closed under +, -, *, contains 0 and 1)
and a K-submodule (closed under + and scalar multiplication). -/
def polynomialSubalgebra : Subalgebra K (PowerSeries K) where
  carrier := {f | IsPolynomial f}
  mul_mem' := isPolynomial_mul
  one_mem' := isPolynomial_one
  add_mem' := isPolynomial_add
  zero_mem' := isPolynomial_zero
  algebraMap_mem' := fun c => by
    simp only [Set.mem_ofPred_eq, IsPolynomial]
    have h : {n : ℕ | PowerSeries.coeff n (algebraMap K (PowerSeries K) c) ≠ 0} ⊆ {0} := by
      intro n hn
      simp only [Set.mem_ofPred_eq, ne_eq] at hn
      simp only [Set.mem_singleton_iff]
      by_contra hne
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, PowerSeries.coeff_one,
        ite_eq_right hne, mul_zero, not_true_eq_false] at hn
    exact Set.Finite.subset (Set.finite_singleton 0) h

/-- The underlying subring of the polynomial subalgebra.
This is the "subring" part of Theorem 7.5.2 (thm.fps.pol.ring):
K[x] is closed under +, -, *, and contains 0 and 1. -/
noncomputable def polynomialSubring : Subring (PowerSeries K) :=
  polynomialSubalgebra.toSubring

/-- The underlying K-submodule of the polynomial subalgebra.
This is the "K-submodule" part of Theorem 7.5.2 (thm.fps.pol.ring):
K[x] is closed under + and scalar multiplication by elements of K. -/
noncomputable def polynomialSubmodule : Submodule K (PowerSeries K) :=
  polynomialSubalgebra.toSubmodule

end FPS
