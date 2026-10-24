/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# x^n-Equivalence of Formal Power Series

This file formalizes the notion of x^n-equivalence of formal power series from
Section `sec.gf.xneq` of the source text.

## Main Definitions

* `PowerSeries.XnEquiv n f g`: Two FPS are x^n-equivalent if their first n+1 coefficients agree.
  This is written as `f ≡ g [mod X^(n+1)]` in the source, and is equivalent to
  `X^(n+1) ∣ (f - g)`.

## Main Results

* `PowerSeries.XnEquiv.equivalence`: x^n-equivalence is an equivalence relation.
* `PowerSeries.XnEquiv.add`: x^n-equivalence is preserved by addition.
* `PowerSeries.XnEquiv.sub`: x^n-equivalence is preserved by subtraction.
* `PowerSeries.XnEquiv.mul`: x^n-equivalence is preserved by multiplication.
* `PowerSeries.XnEquiv.smul`: x^n-equivalence is preserved by scalar multiplication.
* `PowerSeries.XnEquiv.invOfUnit`: x^n-equivalence is preserved by inversion (for invertible FPS).
* `PowerSeries.XnEquiv.sum`: x^n-equivalence is preserved by finite sums.
* `PowerSeries.XnEquiv.prod`: x^n-equivalence is preserved by finite products.
* `PowerSeries.xnEquiv_iff_dvd`: f ≡ g [mod X^(n+1)] iff X^(n+1) ∣ (f - g).
* `PowerSeries.XnEquiv.comp`: x^n-equivalence is preserved by composition (with constant term 0).

## Implementation Notes

We define x^n-equivalence in terms of coefficient equality rather than divisibility,
as this is more directly usable in proofs. The equivalence to divisibility is
established in `xnEquiv_iff_dvd`.

The definition uses `n` for the degree, so `XnEquiv n f g` means the first `n+1`
coefficients agree (i.e., coefficients 0, 1, ..., n).

## References

* Section `sec.gf.xneq` (x^n-equivalence) of the source text.

## Tags

power series, equivalence, truncation, congruence
-/

noncomputable section

open Polynomial Finset

namespace PowerSeries

variable {R : Type*} [CommSemiring R]
/-! ### Definition of x^n-equivalence -/


/-- Two formal power series are x^n-equivalent if their first n+1 coefficients agree.
This corresponds to Definition `def.fps.xneq` in the source text.

We say `XnEquiv n f g` to mean that for all m ∈ {0, 1, ..., n},
we have `[x^m] f = [x^m] g`. -/
def XnEquiv (n : ℕ) (f g : R⟦X⟧) : Prop :=
  ∀ m ≤ n, coeff m f = coeff m g

/-- Notation for x^n-equivalence: `f ≡[x^n] g` means `XnEquiv n f g`.
This notation is used throughout the limits and infinite products theory. -/
notation:50 f " ≡[x^" n "] " g => XnEquiv n f g
/-! ### Basic properties: Equivalence relation (Theorem thm.fps.xneq.props (a)) -/
/-! ### Simp lemmas for basic cases -/
/-! ### Algebraic properties (Theorem thm.fps.xneq.props (b), (c)) -/
/-! ### Inversion (Theorem thm.fps.xneq.props (d)) -/
/-! ### Finite sums and products (Theorem thm.fps.xneq.props (f)) -/


variable {ι : Type*}
/-! ### Characterization via divisibility (Proposition prop.fps.xneq-multiple)

This section proves `prop.fps.xneq-multiple`: Two FPS f and g satisfy
f ≡ g [mod X^(n+1)] if and only if the FPS f - g is a multiple of X^(n+1).
-/
/-! ### Truncation characterization -/
/-! ### Powers -/
/-! ### Composition (Proposition prop.fps.xneq.comp) -/
/-! ### Connection to equality -/

end PowerSeries
