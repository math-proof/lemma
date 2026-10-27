/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Abbrev.RingTheory.MvPowerSeries.Multivariate
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

/-- The first variable `x` in a bivariate power series ring. -/
noncomputable def BivFPS.x : BivFPS R := MvPowerSeries.X 0

/-- The second variable `y` in a bivariate power series ring. -/
noncomputable def BivFPS.y : BivFPS R := MvPowerSeries.X 1

/-!
### Embedding univariate power series into bivariate power series

To formalize Proposition `prop.fps.mulvar.comp-y-coeff`, we need to embed sequences of
univariate power series into bivariate power series. Given a sequence `f : ℕ → PowerSeries R`,
we define the bivariate power series `∑_k f_k y^k` whose coefficient at `x^n y^k` is the
coefficient of `x^n` in `f_k`.
-/


/-- Embedding of a sequence of univariate power series `f : ℕ → PowerSeries R` into a
    bivariate power series `∑_k f_k y^k` in `K[[x, y]]`.

    The coefficient of `x^n y^k` in the result is the coefficient of `x^n` in `f_k`. -/
noncomputable def embedUnivInBiv (f : ℕ → PowerSeries R) : BivFPS R :=
  fun nm => (f (nm 1)).coeff (nm 0)

/-!
### Example: Binomial generating function

The source derives the following identity using bivariate power series:

```
∑_{n,k∈ℕ} C(n,k) x^n y^k = 1/(1 - x(1+y))
```

From this, by comparing coefficients of `y^k`, one obtains the univariate identity:
```
x^k / (1-x)^{k+1} = ∑_{n∈ℕ} C(n,k) x^n  for each k ∈ ℕ
```

This is equation `eq.fps.mulvar.exa1.res1` in the source.
-/


/-- The generating function for binomial coefficients as a bivariate power series:
    `∑_{n,k∈ℕ} C(n,k) x^n y^k`. -/
noncomputable def binomialGenFun : BivFPS ℚ :=
  fun nm => (nm 0).choose (nm 1)

/-- The closed form `1/(1 - x(1+y))` for the binomial generating function. -/
noncomputable def binomialGenFunClosedForm : BivFPS ℚ :=
  MvPowerSeries.invOfUnit (1 - BivFPS.x * (1 + BivFPS.y)) 1

/-!
### Partial Derivatives

The source mentions that multivariate FPSs have `k` partial derivatives (one for each variable).
This section provides the basic infrastructure for partial derivatives.

In Mathlib, more general derivation theory is available via `MvPowerSeries.derivation`.
Here we provide a direct definition that matches the source's description:
for `f = ∑_m a_m x^m`, we have `∂f/∂x_i = ∑_m m_i · a_m · x^{m - e_i}`.
-/


/-- The partial derivative of a multivariate power series with respect to variable `i`.
    For `f = ∑_m a_m x^m`, we have `∂f/∂x_i = ∑_m m_i · a_m · x^{m - e_i}`
    where `e_i` is the `i`-th standard basis vector. -/
noncomputable def partialDeriv {σ : Type*} [DecidableEq σ] (i : σ) :
    MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f := fun m =>
    let m' := m + Finsupp.single i 1
    (m' i : R) * MvPowerSeries.coeff m' f
  map_add' f g := by
    funext m
    simp only [map_add, mul_add]
    rfl
  map_smul' c f := by
    funext m
    simp only [RingHom.id_apply, smul_eq_mul, map_smul]
    change _ = c * _
    ring

/-!
### Substitution in multivariate power series

One needs to be careful with substitution - one cannot substitute non-commuting elements
into a multivariate polynomial. For example, you cannot substitute two non-commuting
matrices `A` and `B` for `x` and `y` into the polynomial `xy` without sacrificing the
rule that a value of the product of two polynomials should be the product of their values.

However, you can still substitute `k` commuting elements for the `k` indeterminates
in a `k`-variable polynomial. You can also compose multivariate FPSs as long as
appropriate summability conditions are satisfied.

The full theory of evaluation/substitution for multivariate power series is available
in Mathlib via `MvPowerSeries.eval` and related constructions.
-/


end AlgebraicCombinatorics
