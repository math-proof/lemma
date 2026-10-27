/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Abbrev.RingTheory.PowerSeries.DividingFPS
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

/-! ### Section: Conventions

We identify each element `a ∈ K` with the constant FPS `(a, 0, 0, 0, ...)`.
In Mathlib, this is handled via the ring homomorphism `algebraMap K (PowerSeries K)`.
-/


noncomputable section

open scoped BigOperators

namespace AlgebraicCombinatorics

variable {K : Type*} [CommRing K]

section PropCommringFracs1

variable {L : Type*} [CommRing L]

/-- Division notation for units: `b / a` means `b * a⁻¹`.
    This formalizes the notation `b/a` for `a` invertible in the text. -/
def divByUnit (b : L) (a : Lˣ) : L := b * (a⁻¹ : Lˣ)

end PropCommringFracs1
end AlgebraicCombinatorics
end
