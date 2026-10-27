/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.FPSDefinition.Part3
import Lemma.PowerSeries.FPSDefinition
/-!
# Substitution and Evaluation of Power Series

This file formalizes the theory of substitution (composition) of formal power series (FPS).

## Main definitions

* `PowerSeries.HasSubst`: The condition for substituting one power series into another.
  In Mathlib, this requires the constant term to be nilpotent. For a commutative ring,
  having constant term 0 suffices.
* `kroneckerDelta`: The Kronecker delta function δᵢⱼ = 1 if i = j, else 0.

## Main results

* `fps_subs_wd_firstCoeffs`: (Proposition 7.3.3a) The first n coefficients of g^n are 0
  when g has constant term 0.
* `fps_subs_wd_summable`: (Proposition 7.3.3b) The sum defining f[g] is well-defined.
* `fps_subs_wd_constCoeff`: (Proposition 7.3.3c) The constant coefficient of f[g] equals f₀.
* `fps_subs_add`: (Proposition 7.3.4a) (f₁ + f₂) ∘ g = f₁ ∘ g + f₂ ∘ g
* `fps_subs_mul`: (Proposition 7.3.4b) (f₁ · f₂) ∘ g = (f₁ ∘ g) · (f₂ ∘ g)
* `fps_subs_div`: (Proposition 7.3.4c) (f₁ / f₂) ∘ g = (f₁ ∘ g) / (f₂ ∘ g)
* `fps_subs_pow`: (Proposition 7.3.4d) f^k ∘ g = (f ∘ g)^k
* `fps_subs_assoc`: (Proposition 7.3.4e) (f ∘ g) ∘ h = f ∘ (g ∘ h)
* `fps_subs_const`: (Proposition 7.3.4f) a ∘ g = a (for constants)
* `fps_subs_X`: (Proposition 7.3.4g) X ∘ g = g ∘ X = g
* `fps_subs_sum`: (Proposition 7.3.4h) (∑ fᵢ) ∘ g = ∑ (fᵢ ∘ g) for finite sums
* `fps_subs_summable`: (Proposition 7.3.4h) Substitution preserves summability
* `fps_subs_summableFPSSum`: (Proposition 7.3.4h) (∑ fᵢ) ∘ g = ∑ (fᵢ ∘ g) for summable families

## Implementation notes

In Mathlib, the substitution `f[g]` is denoted `PowerSeries.subst g f` (note the order reversal).
The condition for substitution is `PowerSeries.HasSubst g`, which requires the constant
coefficient of `g` to be nilpotent. For power series over a reduced ring (like a field),
this is equivalent to having constant term 0.

The source text uses the notation `f[g]` for substituting g into f, which corresponds
to `PowerSeries.subst g f` in Mathlib.

## References

* Source: AlgebraicCombinatorics/tex/FPS/Substitution.tex
* Definition 7.3.1 (def.fps.subs)
* Definition 7.3.6 (def.kron-delta)
* Proposition 7.3.3 (prop.fps.subs.wd)
* Proposition 7.3.4 (prop.fps.subs.rules)
* Lemma 7.3.5 (lem.fps.fg-coeffs-0)
-/


namespace AlgebraicCombinatorics

open PowerSeries

open AlgebraicCombinatorics.FPS (SummableFPS summableFPSSum coeff_summableFPSSum)

variable {K : Type*} [CommRing K]

/-! ## Section: Defining substitution

Definition 7.3.1 (def.fps.subs): Let f and g be two FPSs in K⟦x⟧. Assume that [x⁰]g = 0.
We define f[g] := ∑_{n∈ℕ} fₙ gⁿ.

In Mathlib, this is `PowerSeries.subst g f` when `PowerSeries.HasSubst g` holds.
The condition `[x⁰]g = 0` implies `HasSubst g` via `HasSubst.of_constantCoeff_zero'`.
-/


/-- **Definition 7.3.1** (def.fps.subs)
The composition/substitution f[g] of power series is defined when g has constant term 0.
This is the Mathlib `PowerSeries.subst` function. -/
noncomputable def fps_comp (f g : K⟦X⟧) (_hg : constantCoeff g = 0) : K⟦X⟧ :=
  PowerSeries.subst g f

/-! ## Section: Well-definedness (Proposition 7.3.3)

Proposition 7.3.3 (prop.fps.subs.wd): Let f and g be two FPSs with [x⁰]g = 0.
(a) For each n∈ℕ, the first n coefficients of g^n are 0.
(b) The sum ∑_{n∈ℕ} fₙ gⁿ is well-defined.
(c) [x⁰](∑_{n∈ℕ} fₙ gⁿ) = f₀.
-/
/-! ## Section: Lemma for first k coefficients (Lemma 7.3.5)

Lemma 7.3.5 (lem.fps.fg-coeffs-0): Let f, g ∈ K⟦x⟧ with [x⁰]g = 0.
If the first k coefficients of f are 0, then the first k coefficients of f ∘ g are 0.
-/
/-! ## Section: Laws of substitution (Proposition 7.3.4)

Proposition 7.3.4 (prop.fps.subs.rules): Composition of FPSs satisfies expected rules.
-/
/-! ### Infinite sum version of Proposition 7.3.4(h)

For the full statement of Proposition 7.3.4(h), we need to work with summable families
of FPS in the sense of Definition def.fps.summable: a family (fᵢ)_{i∈I} is summable
if for each coefficient index n, all but finitely many i have [x^n]fᵢ = 0.

Note: SummableFPS, summableFPSSum, and coeff_summableFPSSum are imported from
FPSDefinition.lean, which is the canonical location for these definitions.
-/
/-! ## Section: Examples

Example 7.3.2 (exa.fps.subs.fibonacci): Substituting x + x² into 1/(1-x) gives
the generating function for shifted Fibonacci numbers.
-/


/-- The geometric series 1 + x + x² + ... = 1/(1-x) -/
noncomputable def geometricSeries {K : Type*} [Field K] : K⟦X⟧ := (1 - X)⁻¹

/-! ## Section: Kronecker delta notation (Definition 7.3.6)

Definition 7.3.6 (def.kron-delta): The Kronecker delta δᵢⱼ is 1 if i = j, 0 otherwise.
This is used in the proofs but is standard notation.

The Kronecker delta is defined as:
```
δᵢⱼ = 1  if i = j
δᵢⱼ = 0  if i ≠ j
```

For example, δ₂₂ = 1 and δ₃₈ = 0.
-/


/-- **Definition 7.3.6** (def.kron-delta)
The Kronecker delta function: δᵢⱼ is 1 if i = j, and 0 otherwise. -/
def kroneckerDelta {α : Type*} [DecidableEq α] (i j : α) : K :=
  if i = j then 1 else 0

end AlgebraicCombinatorics
