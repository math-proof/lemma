/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.series.formal.Limits
/-!
# Infinite Products of Formal Power Series

This file formalizes the theory of infinite products of formal power series (FPS),
following the treatment in the source material (Section `sec.gf.prod`).

## Relationship with `InfiniteProducts1.lean`

This file (`InfiniteProducts.lean`) provides the primary API in the `PowerSeries` namespace.
The file `InfiniteProducts1.lean` provides an alternative formalization in the `AlgebraicCombinatorics.FPS`
namespace with **definitionally equivalent** definitions:

* `PowerSeries.Multipliable a` = `AlgebraicCombinatorics.FPS.Multipliable a`
* `PowerSeries.tprod a h` = `AlgebraicCombinatorics.FPS.infprod a h`
* `PowerSeries.DeterminesCoeffInProd a M n` = `AlgebraicCombinatorics.FPS.DeterminesCoeff a n M` (argument order)
* `PowerSeries.IsXnApproximator a M n` = `AlgebraicCombinatorics.FPS.IsXnApproximator a n M` (argument order)

The `PowerSeries` namespace versions are canonical and recommended for new code.

## Main Definitions

* `PowerSeries.DeterminesCoeffInProd`: A finite subset `M` determines the `x^n`-coefficient
  in the product of a family if adding more factors doesn't change that coefficient.
* `PowerSeries.CoeffFinitelyDeterminedInProd`: The `x^n`-coefficient is finitely determined
  if some finite subset determines it.
* `PowerSeries.Multipliable`: A family of FPS is multipliable if all coefficients in its
  product are finitely determined.
* `PowerSeries.tprod`: The infinite product of a multipliable family.
* `PowerSeries.IsXnApproximator`: A finite subset that determines the first `n+1` coefficients.

## Main Results

* `PowerSeries.multipliable_coeff_eq_of_determines`: The infinite product is well-defined.
* `PowerSeries.tprod_coeff`: The coefficient of the infinite product equals the coefficient
  of any determining finite partial product.
* `PowerSeries.multipliable_one_add_of_summable`: If `(f_i)` is summable, then `(1 + f_i)` is multipliable.
* `PowerSeries.multipliable_of_finite_ne_one`: If all but finitely many entries equal 1,
  the family is multipliable.
* `PowerSeries.multipliable_of_union`: Products can be split into subproducts.
* `PowerSeries.multipliable_mul`: Products of multipliable families are multipliable.
* `PowerSeries.multipliable_div`: Quotients of multipliable families (with invertible denominators).
* `PowerSeries.multipliable_subfamily`: Subfamilies of multipliable families of invertible FPS.
* `PowerSeries.multipliable_reindex`: Reindexing preserves multipliability.
* `PowerSeries.tprod_fubini`: Fubini rule for infinite products (I × J → I then J).
* `PowerSeries.tprod_fubini_J`: Fubini rule for infinite products (I × J → J then I).
* `PowerSeries.fubini_prod_invertible`: Fubini rule showing both row/column families are multipliable.

## References

* Source: `AlgebraicCombinatorics/tex/FPS/InfiniteProducts1.tex`
-/


open scoped BigOperators

namespace PowerSeries

variable {R : Type*} [CommRing R]
variable {I : Type*}
/-!
### Motivating Example: Binary Representation

The product `∏_{i ∈ ℕ} (1 + x^{2^i})` equals `1/(1-x)` in `R[[x]]`.
This relates to the unique binary representation of natural numbers.
(Label: eq.fps.prod.binary.2)
-/
/-!
### Definition of Coefficient Determination

Definition \ref{def.fps.determines-xn-coeff}
-/


/-- A finite subset `M` of `I` determines the `x^n`-coefficient in the product of
a family `(a_i)_{i ∈ I}` if for every finite superset `J` of `M`, the `x^n`-coefficient
of `∏_{i ∈ J} a_i` equals that of `∏_{i ∈ M} a_i`.
(Label: def.fps.determines-xn-coeff part (b)) -/
def DeterminesCoeffInProd (a : I → PowerSeries R) (M : Finset I) (n : ℕ) : Prop :=
  ∀ J : Finset I, M ⊆ J → (∏ i ∈ J, a i).coeff n = (∏ i ∈ M, a i).coeff n

/-- A finite subset `M` of `I` determines the `x^n`-coefficient in the sum of
a family `(a_i)_{i ∈ I}` if for every finite superset `J` of `M`, the `x^n`-coefficient
of `∑_{i ∈ J} a_i` equals that of `∑_{i ∈ M} a_i`.
(Label: def.fps.determines-xn-coeff part (a)) -/
def DeterminesCoeffInSum (a : I → PowerSeries R) (M : Finset I) (n : ℕ) : Prop :=
  ∀ J : Finset I, M ⊆ J → (∑ i ∈ J, a i).coeff n = (∑ i ∈ M, a i).coeff n
/-!
### Definition of Finitely Determined Coefficients

Definition \ref{def.fps.xn-coeff-fin-determined}
-/


/-- The `x^n`-coefficient in the product of `(a_i)_{i ∈ I}` is finitely determined
if there exists a finite subset `M` that determines it.
(Label: def.fps.xn-coeff-fin-determined part (b)) -/
def CoeffFinitelyDeterminedInProd (a : I → PowerSeries R) (n : ℕ) : Prop :=
  ∃ M : Finset I, DeterminesCoeffInProd a M n

/-- The `x^n`-coefficient in the sum of `(a_i)_{i ∈ I}` is finitely determined
if there exists a finite subset `M` that determines it.
(Label: def.fps.xn-coeff-fin-determined part (a)) -/
def CoeffFinitelyDeterminedInSum (a : I → PowerSeries R) (n : ℕ) : Prop :=
  ∃ M : Finset I, DeterminesCoeffInSum a M n
/-!
### API for Finitely Determined Coefficients

Basic lemmas for `CoeffFinitelyDeterminedInProd` and `CoeffFinitelyDeterminedInSum`.
(Label: def.fps.xn-coeff-fin-determined)
-/
/-!
### Summability and Finite Determination

Proposition \ref{prop.fps.summable=fin-det}
-/
/-!
### Multipliability

Definition \ref{def.fps.multipliable}
-/


/-- A family `(a_i)_{i ∈ I}` of FPS is multipliable if for each `n ∈ ℕ`,
the `x^n`-coefficient in its product is finitely determined.
(Label: def.fps.multipliable part (a)) -/
def Multipliable (a : I → PowerSeries R) : Prop :=
  ∀ n : ℕ, CoeffFinitelyDeterminedInProd a n
/-!
### The Infinite Product

Definition \ref{def.fps.multipliable} part (b)
-/


/-- For a multipliable family, the `n`-th coefficient of the infinite product.
This is the common value of `(∏ i ∈ M, a i).coeff n` for any finite `M` that
determines the `x^n`-coefficient.
(Label: def.fps.multipliable part (b)) -/
noncomputable def tprodCoeff (a : I → PowerSeries R) (ha : Multipliable a) (n : ℕ) : R :=
  (∏ i ∈ (ha n).choose, a i).coeff n

/-- The infinite product of a multipliable family of formal power series.
For a multipliable family `(a_i)_{i ∈ I}`, this is the FPS whose `x^n`-coefficient
equals the `x^n`-coefficient of any finite partial product that determines it.
(Label: def.fps.multipliable part (b)) -/
noncomputable def tprod (a : I → PowerSeries R) (ha : Multipliable a) : PowerSeries R :=
  PowerSeries.mk (fun n => tprodCoeff a ha n)
/-!
### x^n-Approximators

Definition \ref{def.fps.infprod-approx}
-/


/-- A finite subset `M` is an `x^n`-approximator for a family `(a_i)_{i ∈ I}`
if it determines the first `n+1` coefficients (i.e., `x^0, x^1, ..., x^n`)
in the product.
(Label: def.fps.infprod-approx) -/
def IsXnApproximator (a : I → PowerSeries R) (M : Finset I) (n : ℕ) : Prop :=
  ∀ m ≤ n, DeterminesCoeffInProd a M m
/-!
### Lemmas on Irrelevant Factors

Lemma \ref{lem.fps.prod.irlv.1}
-/
/-!
### Criterion for Multipliability

Theorem \ref{thm.fps.1+f-mulable}
-/
/-!
### Simple Criteria for Multipliability

Proposition \ref{prop.fps.1-mulable} and Remark \ref{rmk.fps.0-mulable}
-/
/-!
### The Binary Product Identity (Infinite Version)

This is the infinite version of the binary product identity, stating that
`∏_{i ∈ ℕ} (1 + x^{2^i}) = 1/(1-x)`.
(Label: eq.fps.prod.binary.2)
-/
/-!
### Properties of Infinite Products

Proposition \ref{prop.fps.union-mulable}
-/
/-!
### Product Rule for Multipliable Families

Proposition \ref{prop.fps.prod-mulable}
-/
/-!
### Division Rule for Multipliable Families

Proposition \ref{prop.fps.div-mulable}
-/
/-!
### Subfamilies of Multipliable Families

Remark \ref{rmk.fps.subfamily-not-mulable} shows that not every subfamily of a
multipliable family is multipliable. However, for invertible FPS, this holds.

Proposition \ref{prop.fps.prods-mulable-subfams}
-/
/-!
### Reindexing

Proposition \ref{prop.fps.prods-mulable-rules.reindex}
-/
/-!
### Breaking Products into Subproducts

Proposition \ref{prop.fps.prods-mulable-rules.SW1}
-/
/-!
### Fubini Rule for Infinite Products

Proposition \ref{prop.fps.prods-mulable-rules.fubini1}
-/

/-- The fiber of `Prod.fst : I × J → I` at `i` is equivalent to `J`. -/
def fiberEquiv (I J : Type*) (i : I) : {p : I × J // Prod.fst p = i} ≃ J where
  toFun := fun ⟨p, _⟩ => p.2
  invFun := fun j => ⟨(i, j), rfl⟩
  left_inv := fun ⟨⟨i', j⟩, hp⟩ => by
    simp only [Subtype.mk.injEq, Prod.mk.injEq, and_true]
    exact hp.symm
  right_inv := fun _ => rfl

/-- The fiber of `Prod.snd : I × J → J` at `j` is equivalent to `I`. -/
def fiberEquivSnd (I J : Type*) (j : J) : {p : I × J // Prod.snd p = j} ≃ I where
  toFun := fun ⟨p, _⟩ => p.1
  invFun := fun i => ⟨(i, j), rfl⟩
  left_inv := fun ⟨⟨i, j'⟩, hp⟩ => by
    simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
    exact hp.symm
  right_inv := fun _ => rfl
/-!
### Approximator Properties

Proposition \ref{prop.fps.infprod-approx-xneq}
-/
/-!
### Approximator Properties in terms of x^n-equivalence

Proposition \ref{prop.fps.infprod-approx-xneq}

These are the same results as above, but stated using the `xnEquiv` relation
(which says two FPS agree on coefficients 0 through n).

Note: The `xnEquiv` definition and basic lemmas (`xnEquiv_refl`, `xnEquiv_symm`, `xnEquiv_trans`)
are imported from `AlgebraicCombinatorics.FPS.Limits`.
-/

end PowerSeries
