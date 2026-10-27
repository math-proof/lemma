/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts
import Notation.RingTheory.PowerSeries.XnEquivalence
open scoped Polynomial
open PowerSeries Finset

/-!
# Infinite Products of Formal Power Series (Part 1)

This file formalizes detailed proofs about infinite products of formal power series,
following the "Details: Infinite products (part 1)" section of the source.

## Relationship with `InfiniteProducts.lean`

This file (`InfiniteProducts1.lean`) re-exports the canonical definitions from
`InfiniteProducts.lean` (in the `PowerSeries` namespace) into the `AlgebraicCombinatorics.FPS` namespace.
The definitions are **definitionally equal**:

* `AlgebraicCombinatorics.FPS.Multipliable` := `PowerSeries.Multipliable`
* `AlgebraicCombinatorics.FPS.infprod` := `PowerSeries.tprod`
* `AlgebraicCombinatorics.FPS.DeterminesCoeff a n U` := `PowerSeries.DeterminesCoeffInProd a U n`
* `AlgebraicCombinatorics.FPS.CoeffFinitelyDetermined` := `PowerSeries.CoeffFinitelyDeterminedInProd`
* `AlgebraicCombinatorics.FPS.IsXnApproximator a n U` := `PowerSeries.IsXnApproximator a U n`

The `PowerSeries` namespace versions are canonical and recommended for new code.
The `AlgebraicCombinatorics.FPS` aliases are provided for consistency with other "Details" files.

**Key difference:** This file contains a fully proved version of SW1 (`multipliable_fiber_prods`,
`infprod_eq_infprod_fiber`) with the invertibility hypothesis (`hinv : ∀ s, IsUnit (constantCoeff (a s))`).
The `InfiniteProducts.lean` file has both:
- Fully proved `multipliable_prod_fibers_inv` / `tprod_eq_tprod_fibers_inv` (with invertibility)
- Sorry'd `multipliable_prod_fibers` / `tprod_eq_tprod_fibers` (without invertibility)

This file is kept separate to:
1. Follow the structure of the TeX source (Details: Infinite products part 1)
2. Provide detailed proofs of specific propositions from the source
3. Use the `AlgebraicCombinatorics.FPS` namespace for consistency with other "Details" files

## Main Definitions

* `AlgebraicCombinatorics.FPS.IsXnApproximator`: Alias for `PowerSeries.IsXnApproximator` with swapped argument order.
  A finite subset `U ⊆ I` is an x^n-approximator for a family `(aᵢ)_{i∈I}` if it determines
  the first `n+1` coefficients of the infinite product. (Definition def.fps.xnappr)

* `AlgebraicCombinatorics.FPS.Multipliable`: Alias for `PowerSeries.Multipliable`.
  A family of FPSs is multipliable if each coefficient in the product is finitely determined.
  (Definition def.fps.multipliable)

* `AlgebraicCombinatorics.FPS.infprod`: Alias for `PowerSeries.tprod`.
  The infinite product of a multipliable family of FPSs. (Definition def.fps.multipliable (b))

## Main Results

### Proposition prop.fps.union-mulable
* `multipliable_of_subset`: If `(aᵢ)_{i∈I}` is multipliable and `J ⊆ I`, then both
  `(aᵢ)_{i∈J}` and `(aᵢ)_{i∈I\J}` are multipliable.
* `infprod_union_eq`: The infinite product over `I` equals the product of
  infinite products over `J` and `I \ J`.

### Proposition prop.fps.prod-mulable
* `multipliable_mul`: If `(aᵢ)` and `(bᵢ)` are multipliable, so is `(aᵢ · bᵢ)`.
* `infprod_mul_eq`: The infinite product of `(aᵢ · bᵢ)` equals the product of
  the infinite products.

### Lemma lem.fps.prod.irlv.cong-div
* `xnEquiv_div`: If `a ≡ b` and `c ≡ d` (mod x^{n+1}) with `c, d` invertible,
  then `a/c ≡ b/d` (mod x^{n+1}).

### Proposition prop.fps.div-mulable
* `multipliable_div`: If `(aᵢ)` and `(bᵢ)` are multipliable with each `bᵢ` invertible,
  then `(aᵢ/bᵢ)` is multipliable.
* `infprod_div_eq`: The infinite product of `(aᵢ/bᵢ)` equals the quotient of
  the infinite products.

### Lemma lem.fps.prods-mulable-subfams-appr
* `xnApproximator_inter`: If `U` is an x^n-approximator for `(aᵢ)_{i∈I}`,
  then `U ∩ J` is an x^n-approximator for `(aᵢ)_{i∈J}`.

### Lemma lem.fps.prods-mulable-rules.SW1.lem1
* `xnEquiv_finprod`: If each `cᵥ ≡ dᵥ` (mod x^{n+1}), then `∏_{v∈V} cᵥ ≡ ∏_{v∈V} dᵥ`.

### Proposition prop.fps.prods-mulable-rules.SW1
* `multipliable_fiber_prods`: Infinite products can be reindexed along a surjection,
  grouping terms by fibers.
* `infprod_eq_infprod_fiber`: The infinite product over the source equals the infinite
  product over the target of fiber products.

## References

* Source: AlgebraicCombinatorics/tex/Details/InfiniteProducts1.tex

## Implementation Notes

This file re-exports the canonical definitions from `PowerSeries` namespace into
`AlgebraicCombinatorics.FPS` namespace using `abbrev`. The definitions are definitionally equal,
so all theorems work seamlessly with either namespace.

The key insight is that a family is multipliable if for each coefficient index `n`,
there exists a finite "approximating" set that determines that coefficient.
-/


namespace AlgebraicCombinatorics

namespace FPS

variable {K : Type*} [CommRing K]

/-!
## x^n-Equivalence (Local Notation)

We use `PowerSeries.XnEquiv` from `XnEquivalence.lean` for the underlying definition.
The notation `f ≡[x^n] g` is imported from `Limits.lean` (via `InfiniteProducts.lean`).
-/
/-!
## Lemma lem.fps.prod.irlv.cong-mul

If `a ≡ b` and `c ≡ d` (mod x^{n+1}), then `a·c ≡ b·d` (mod x^{n+1}).
This is used in the proof of Proposition prop.fps.prod-mulable.
-/
/-!
## Lemma lem.fps.prod.irlv.cong-div

If `a ≡ b` and `c ≡ d` (mod x^{n+1}) with `c, d` invertible,
then `a/c ≡ b/d` (mod x^{n+1}).

This is the division analogue of lem.fps.prod.irlv.cong-mul.
-/
/-!
## x^n-Approximators and Multipliable Families

The definitions below are aliases for the canonical `PowerSeries` versions.
They are provided for consistency with other "Details" files and to maintain
the argument order used in this file.
-/


/-- Alias for `PowerSeries.DeterminesCoeffInProd` with swapped argument order.
    A finite subset `U ⊆ I` determines the x^n-coefficient in the product of `(aᵢ)_{i∈I}`
    if for every finite subset `T` with `U ⊆ T ⊆ I`, the x^n-coefficient of `∏_{i∈T} aᵢ`
    equals that of `∏_{i∈U} aᵢ`.
    (Definition def.fps.infprod.coeff-det) -/
abbrev DeterminesCoeff {ι : Type*} (a : ι → K⟦X⟧) (n : ℕ) (U : Finset ι) : Prop :=
  PowerSeries.DeterminesCoeffInProd a U n

/-- Alias for `PowerSeries.IsXnApproximator` with swapped argument order.
    A finite subset `U ⊆ I` is an x^n-approximator for `(aᵢ)_{i∈I}` if it determines
    the first `n+1` coefficients in the product.
    (Definition def.fps.xnappr)
    Label: def.fps.xnappr -/
abbrev IsXnApproximator {ι : Type*} (a : ι → K⟦X⟧) (n : ℕ) (U : Finset ι) : Prop :=
  PowerSeries.IsXnApproximator a U n

/-- Alias for `PowerSeries.CoeffFinitelyDeterminedInProd`.
    The x^n-coefficient in the product of `(aᵢ)_{i∈I}` is finitely determined if
    there exists a finite subset that determines it.
    (Definition def.fps.infprod.coeff-det) -/
abbrev CoeffFinitelyDetermined {ι : Type*} (a : ι → K⟦X⟧) (n : ℕ) : Prop :=
  PowerSeries.CoeffFinitelyDeterminedInProd a n

/-- Alias for `PowerSeries.Multipliable`.
    A family `(aᵢ)_{i∈I}` of FPSs is multipliable if each coefficient in the product
    is finitely determined.
    (Definition def.fps.multipliable)
    Label: def.fps.multipliable -/
abbrev Multipliable {ι : Type*} (a : ι → K⟦X⟧) : Prop :=
  PowerSeries.Multipliable a

/-!
## The Infinite Product

The infinite product definitions are aliases for the canonical `PowerSeries` versions.
-/


/-- Alias for `PowerSeries.tprodCoeff`.
    The n-th coefficient of the infinite product of a multipliable family.
    This is well-defined because the coefficient is finitely determined. -/
noncomputable abbrev infprodCoeff {ι : Type*} (a : ι → K⟦X⟧) (h : Multipliable a) (n : ℕ) : K :=
  PowerSeries.tprodCoeff a h n

/-- Alias for `PowerSeries.tprod`.
    The infinite product of a multipliable family of FPSs.
    (Definition def.fps.multipliable (b))
    Label: def.fps.multipliable -/
noncomputable abbrev infprod {ι : Type*} (a : ι → K⟦X⟧) (h : Multipliable a) : K⟦X⟧ :=
  PowerSeries.tprod a h

end FPS
end AlgebraicCombinatorics
