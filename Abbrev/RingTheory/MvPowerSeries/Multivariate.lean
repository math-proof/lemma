/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
open MvPowerSeries Finset BigOperators Finsupp

variable {R : Type*} [CommSemiring R]

/-!
# Multivariate Formal Power Series

This file formalizes the material from Section `sec.gf.multivar` on multivariate formal power
series (FPSs).

## Main Content

Multivariate FPSs are FPSs in several variables. Their theory is mostly analogous to the theory
of univariate FPSs, but requires more subscripts. In Mathlib, multivariate formal power series
are defined as `MvPowerSeries σ R := (σ →₀ ℕ) → R`, where `σ` is the index set of variables.

### Key concepts from the source:

- **Bivariate FPSs**: FPSs in two variables `x` and `y` have the form `∑_{i,j∈ℕ} a_{i,j} x^i y^j`.
  In Mathlib, this is `MvPowerSeries (Fin 2) R`.

- **Multiplication**: For any two FPSs `a` and `b` and any `n ∈ ℕ^k`:
  `[x^n](ab) = ∑_{i+j=n} [x^i]a · [x^j]b`
  This is already captured by `MvPowerSeries.coeff_mul`.

- **Indeterminates**: The indeterminate `x_i` is defined as the family with a single `1` at
  position `(0,...,0,1,0,...,0)` (with `1` in the `i`-th position).
  This is `MvPowerSeries.X i` in Mathlib.

- **Partial derivatives**: Instead of one derivative, there are `k` partial derivatives
  (one for each variable).

## Main Results

- `embedUnivInBiv`: Embedding of sequences of univariate power series into bivariate power series
- `eq_of_embedUnivInBiv_eq`: Proposition `prop.fps.mulvar.comp-y-coeff` -
  if `∑_k f_k y^k = ∑_k g_k y^k` in `K[[x,y]]`, then `f_k = g_k` for each `k`.
- `binomialGenFun_eq`: The generating function identity
  `∑_{n,k∈ℕ} C(n,k) x^n y^k = 1/(1-x(1+y))`
- `binomialGenFun_xyk_eq`: Equation `eq.fps.mulvar.exa1.xyk` - the intermediate bivariate equation
- `sum_choose_pow_eq`: Equation `eq.fps.mulvar.exa1.res1` - the univariate identity derived from
  comparing coefficients
- `partialDeriv`: Partial derivative of a multivariate power series
- `partialDeriv_mul`: The product rule for partial derivatives

## References

* Section `sec.gf.multivar` of the source text

## TODO

The source notes that this section needs more details.
-/


namespace AlgebraicCombinatorics

/-!
### Notation for multivariate power series rings

The `K`-algebra of all FPSs in `k` variables `x₁, x₂, ..., xₖ` over `K` is denoted
by `K[[x₁, x₂, ..., xₖ]]` in the source. In Mathlib, this is `MvPowerSeries (Fin k) K`.
-/


/-- The algebra of formal power series in `k` variables over `R`.
    This corresponds to `K[[x₁, x₂, ..., xₖ]]` in the source notation. -/
abbrev FPS (k : ℕ) (R : Type*) [CommSemiring R] := MvPowerSeries (Fin k) R

/-- The algebra of formal power series in 2 variables (bivariate).
    This corresponds to `K[[x, y]]` in the source. -/
abbrev BivFPS (R : Type*) [CommSemiring R] := MvPowerSeries (Fin 2) R

end AlgebraicCombinatorics
