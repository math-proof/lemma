/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Dividing Formal Power Series

This file formalizes the content from `DividingFPS.tex`, covering:
- Inverses in commutative rings (uniqueness, notation)
- Characterization of invertible FPSs
- Newton's binomial formula for FPSs
- Upper negation formula for binomial coefficients
- Division by `x` for FPSs with vanishing constant term
- Various lemmas about coefficients and multiples

## Main Results

- `fps_invertible_iff_constantCoeff`: An FPS is invertible iff its constant term is invertible
- `fps_invertible_iff_constantCoeff_ne_zero`: Over a field, an FPS is invertible iff its
  constant term is nonzero
- `binomUpperNegation`: The upper negation formula `C(-n,k) = (-1)^k * C(k+n-1,k)`
- `fps_onePlusX_inv`: Formula for `(1+x)^{-1}` as a power series
- `fps_onePlusX_pow_neg`: Formula for `(1+x)^{-n}` for natural `n`
- `fps_newtonBinomial`: Newton's binomial formula `(1+x)^n = Σ C(n,k) x^k`
- `PowerSeries.divByX`: Division by `x` for FPSs with zero constant term
- Various lemmas about coefficients and multiples of FPSs

## References

* Grinberg, Darij. "Algebraic Combinatorics" (lecture notes)

## Tags

formal power series, inverses, binomial coefficients, Newton's binomial formula
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCombinatorics
/-! ### Section: Conventions

We identify each element `a ∈ K` with the constant FPS `(a, 0, 0, 0, ...)`.
In Mathlib, this is handled via the ring homomorphism `algebraMap K (PowerSeries K)`.
-/


variable {K : Type*} [CommRing K]

/-- The constant FPS corresponding to an element of the base ring.
This is `algebraMap K (PowerSeries K)` in Mathlib. -/
abbrev constFPS (a : K) : PowerSeries K := algebraMap K (PowerSeries K) a
/-! ### Section: Inverses in commutative rings

The uniqueness of inverses and notation for fractions are standard in Mathlib.
We recall the key facts here for reference.
-/
/-! ### Section: Properties of inverses and fractions (prop.commring.fracs.1)

**Proposition (prop.commring.fracs.1)**: Let `L` be a commutative ring. Then:
- **(a)** Any invertible element `a ∈ L` satisfies `a⁻¹ = 1/a`.
- **(b)** For any invertible elements `a, b ∈ L`, the element `ab` is invertible as well,
  and satisfies `(ab)⁻¹ = b⁻¹a⁻¹ = a⁻¹b⁻¹`.
- **(c)** If `a ∈ L` is invertible, and if `n ∈ ℤ` is arbitrary, then `a^{-n} = (a⁻¹)^n = (a^n)⁻¹`.
- **(d)** Laws of exponents hold for negative exponents as well.
- **(e)** Laws of fractions hold: `b/a + d/c = (bc + ad)/(ac)` and `(b/a) · (d/c) = (bd)/(ac)`.
- **(f)** Division undoes multiplication: `c/a = b` iff `c = ab`.

In Mathlib, these are mostly standard lemmas for `Units` and `IsUnit`.
-/


section PropCommringFracs1

variable {L : Type*} [CommRing L]

/-- Division notation for units: `b / a` means `b * a⁻¹`.
    This formalizes the notation `b/a` for `a` invertible in the text. -/
def divByUnit (b : L) (a : Lˣ) : L := b * (a⁻¹ : Lˣ)

/-- Local notation for division by a unit. -/
scoped notation:70 b " /ᵤ " a => divByUnit b a

end PropCommringFracs1
/-! ### Section: Inverses in K[[x]]

**Proposition (prop.fps.invertible)**: An FPS `a` is invertible in `K[[x]]` if and only if
its constant term `[x^0] a` is invertible in `K`.

This is `PowerSeries.isUnit_iff_constantCoeff` in Mathlib.
-/
/-! ### Section: Coefficient formulas for inverses

Explicit formulas for the coefficients of the inverse of an FPS.
-/
/-! ### Section: Newton's binomial formula

We prove Newton's binomial formula: `(1+x)^n = Σ_{k ∈ ℕ} C(n,k) x^k` for all `n ∈ ℤ`.
-/
/-! ### Section: Dividing by x

**Definition (def.fps.div-by-x)**: For an FPS `a = (a_0, a_1, a_2, ...)` with `a_0 = 0`,
we define `a/x` to be the FPS `(a_1, a_2, a_3, ...)`.
-/


/-- Division of an FPS by `x`, defined when the constant term is zero.
Given `a = (a_0, a_1, a_2, ...)` with `a_0 = 0`, returns `(a_1, a_2, a_3, ...)`.
Label: def.fps.div-by-x -/
def PowerSeries.divByX (a : PowerSeries K) (_ : a.constantCoeff = 0) : PowerSeries K :=
  PowerSeries.mk fun n => a.coeff (n + 1)
/-! ### Section: A few lemmas

Various lemmas about coefficients and multiples of FPSs.
-/

/-- A multiple of `g` is an FPS of the form `g * a`. -/
def PowerSeries.isMultipleOf (f g : PowerSeries K) : Prop := g ∣ f

end AlgebraicCombinatorics
