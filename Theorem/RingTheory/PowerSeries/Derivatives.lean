/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.FPSDefinition.Part3
import Lemma.PowerSeries.FPSDefinition
open PowerSeries Polynomial
open scoped PowerSeries
open AlgebraicCombinatorics.FPS (SummableFPS summableFPSSum coeff_summableFPSSum)

namespace AlgebraicCombinatorics.FPS
section Definition

variable {R : Type*} [CommSemiring R]
end Definition
section DerivativeRules

variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [CommRing R']
variable {K : Type*} [Field K]
variable {A : Type*} [CommRing A]
end DerivativeRules
section Additional

variable {R : Type*} [CommSemiring R]

end Additional

end AlgebraicCombinatorics.FPS
/-!
# Derivatives of Formal Power Series

This file formalizes the theory of derivatives of formal power series (FPS) from
`AlgebraicCombinatorics/tex/FPS/Derivatives.tex`.

## Main Results

The derivative of a formal power series `f = ∑ fₙ xⁿ` is defined as `f' = ∑ n · fₙ · x^(n-1)`.

Mathlib already provides `PowerSeries.derivative` as a derivation on `R⟦X⟧`. We document
the correspondence with the textbook theorems and provide any additional results.

### Derivative Rules (Theorem thm.fps.deriv.rules)

* **(a)** `(f + g)' = f' + g'` — `derivative_add`
* **(b)** Summable families: `(∑ fᵢ)' = ∑ fᵢ'` — `derivative_sum`, `derivative_summableFPSSum`
* **(c)** `(c · f)' = c · f'` — `derivative_smul`, `derivative_C_mul`
* **(d)** `(f · g)' = f' · g + f · g'` — `derivative_mul` (Leibniz rule)
* **(e)** `(f / g)' = (f' · g - f · g') / g²` — `derivative_div` (quotient rule)
* **(f)** `(g^n)' = n · g^(n-1) · g'` — `derivative_pow'` (power rule)
* **(g)** `(f ∘ g)' = (f' ∘ g) · g'` — `derivative_comp` (chain rule)
* **(h)** If `f' = g'`, then `f - g` is constant — `derivative_eq_imp_diff_const`

## References

* Mathlib: `Mathlib.RingTheory.PowerSeries.Derivative`
* Source: `AlgebraicCombinatorics/tex/FPS/Derivatives.tex`

-/


/-!
## Definition of Derivative

The derivative of a formal power series is already defined in Mathlib as
`PowerSeries.derivative : Derivation R R⟦X⟧ R⟦X⟧`.

For `f = ∑ fₙ xⁿ`, we have `f' = ∑ (n+1) · f_{n+1} · xⁿ`, or equivalently,
the n-th coefficient of `f'` is `(n+1) · f_{n+1}`.

This matches Definition def.fps.deriv from the source.
-/


/-!
### Definition def.fps.deriv

For `f = ∑ fₙ xⁿ`, the textbook defines `f' := ∑_{n>0} n · fₙ · x^{n-1}`.

Reindexing with m = n-1 (so n = m+1), this becomes:
`f' = ∑_{m≥0} (m+1) · f_{m+1} · x^m`

This is exactly `PowerSeries.derivativeFun` from Mathlib, which defines:
`derivativeFun f := mk (fun n => coeff (n + 1) f * (n + 1))`

The derivative is then packaged as a `Derivation R R⟦X⟧ R⟦X⟧`.
-/

/-!
## Theorem thm.fps.deriv.rules: Derivative Rules

We document the correspondence between the textbook theorems and Mathlib.
-/


/-!
### Part (a): Additivity

`(f + g)' = f' + g'`

This is automatic since `derivative` is a `Derivation`, hence an additive map.
-/
/-!
### Part (b): Summable Families

If `(fᵢ)_{i ∈ I}` is a summable family of FPSs, then `(∑ fᵢ)' = ∑ fᵢ'`.

We first state it for finite sums (which follows from additivity), then for
infinite summable families (where summability means that for each coefficient
index, only finitely many family members have nonzero coefficient).
-/

-- Note: SummableFPS and summableFPSSum are imported from FPSDefinition.lean
-- The following uses the canonical definitions from that file.
-- These require [CommRing R] rather than [CommSemiring R]

/-!
### Part (c): Scalar Multiplication

`(c · f)' = c · f'`

This is automatic since `derivative` is an `R`-linear map.
-/
/-!
### Part (d): Leibniz Rule (Product Rule)

`(f · g)' = f' · g + f · g'`

This is the defining property of a derivation.
-/
/-!
### Part (e): Quotient Rule

`(f / g)' = (f' · g - f · g') / g²` for invertible `g`.

In Mathlib, this is expressed using `PowerSeries.derivative_inv'` for fields,
or `PowerSeries.derivative_inv` for units.
-/


/-!
### Part (f): Power Rule

`(g^n)' = n · g^(n-1) · g'`

This is `PowerSeries.derivative_pow` in Mathlib.
-/


/-!
### Part (g): Chain Rule

`(f ∘ g)' = (f' ∘ g) · g'` when composition is defined.

In Mathlib, composition is `PowerSeries.subst`, and this is `PowerSeries.derivative_subst`.
The condition for substitution is that `g` has nilpotent constant term (which includes
the case when `[x⁰]g = 0`).
-/
/-!
### Part (h): Uniqueness of Antiderivatives

If `f' = g'` and `K` is a ℚ-algebra, then `f - g` is constant.

In Mathlib, this is `PowerSeries.derivative.ext` (with the converse direction:
if derivatives and constant terms match, then the series are equal).
-/

/-!
## Additional Results

Some useful consequences and special cases.
-/


