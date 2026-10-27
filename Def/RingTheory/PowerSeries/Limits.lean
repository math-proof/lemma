/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Notation.RingTheory.PowerSeries.XnEquivalence
open scoped Polynomial

/-!
# Limits of Formal Power Series

This file formalizes the notion of coefficientwise limits of formal power series,
following Section 7.5 of Loehr's "Bijective Combinatorics".

## Main Definitions

* `Seq.StabilizesTo`: A sequence `(a_i)_{i ∈ ℕ}` stabilizes to `a` if there exists `N`
  such that for all `i ≥ N`, we have `a_i = a`. (Definition 7.5.1)
* `PowerSeries.CoeffStabilizesTo`: A sequence of FPSs `(f_i)` coefficientwise stabilizes
  to `f` if for each `n ∈ ℕ`, the sequence of `n`-th coefficients stabilizes.
  (Definition 7.5.2)

## Main Results

* `PowerSeries.coeffStabilizesTo_of_forall_coeff_stabilizes`: If each coefficient sequence
  stabilizes, then the FPS sequence coefficientwise stabilizes. (Theorem 7.5.3)
* `PowerSeries.exists_xnEquiv_of_coeffStabilizesTo`: If `f_i → f`, then for each `n`,
  eventually `f_i ≡ f (mod x^{n+1})`. (Lemma 7.5.4)
* `PowerSeries.coeffStabilizesTo_add`: Limits respect addition. (Proposition 7.5.5)
* `PowerSeries.coeffStabilizesTo_mul`: Limits respect multiplication. (Proposition 7.5.5)
* `PowerSeries.coeffStabilizesTo_div`: Limits respect division. (Proposition 7.5.6)
* `PowerSeries.coeffStabilizesTo_comp`: Limits respect composition. (Proposition 7.5.7)
* `PowerSeries.coeffStabilizesTo_derivative`: Limits respect derivatives. (Proposition 7.5.8)
* `PowerSeries.coeffStabilizesTo_sum`: Infinite sum is limit of partial sums. (Theorem 7.5.9)
* `PowerSeries.coeffStabilizesTo_prod`: Infinite product is limit of partial products.
  (Theorem 7.5.10)
* `PowerSeries.fps_eq_limit_of_polynomials`: Each FPS is a limit of polynomials.
  (Corollary 7.5.11)

## Relationship with InfiniteProducts.lean

This file also defines `IsMultipliable` and `tprod'` for ℕ-indexed sequences of FPS.
These are **more restrictive** than the general `PowerSeries.Multipliable` and
`PowerSeries.tprod` in `InfiniteProducts.lean`:

* `IsMultipliable f` requires: (1) all constant terms equal 1, AND (2) eventually
  all terms are 1 + O(x^{n+1}) for each n.
* `PowerSeries.Multipliable a` only requires that each coefficient is finitely determined.

The `IsMultipliable`/`tprod'` definitions are used specifically for limits of partial
products (where the index is ℕ and we consider products `∏_{i=0}^{N} f_i`).
For general infinite products over arbitrary index types, use the definitions in
`InfiniteProducts.lean`.

## References

* [Loehr, *Bijective Combinatorics*, Section 7.5]
-/


namespace Seq

variable {K : Type*}

/-- A sequence `(a_i)_{i ∈ ℕ}` stabilizes to `a` if there exists `N` such that
for all `i ≥ N`, we have `a_i = a`.

This is the notion of convergence in the discrete topology.
(Definition 7.5.1, label: def.fps.lim.stab) -/
def StabilizesTo (a : ℕ → K) (lim : K) : Prop :=
  ∃ N : ℕ, ∀ i ≥ N, a i = lim

end Seq

namespace PowerSeries

variable {K : Type*} [CommRing K]

/-- A sequence of FPSs `(f_i)_{i ∈ ℕ}` coefficientwise stabilizes to `f` if for each `n ∈ ℕ`,
the sequence `([x^n] f_i)_{i ∈ ℕ}` stabilizes to `[x^n] f`.

This is the notion of convergence in the product topology where each factor `K`
has the discrete topology.
(Definition 7.5.2, label: def.fps.lim.coeff-stab) -/
def CoeffStabilizesTo (f : ℕ → PowerSeries K) (lim : PowerSeries K) : Prop :=
  ∀ n : ℕ, Seq.StabilizesTo (fun i => coeff n (f i)) (coeff n lim)

end PowerSeries
