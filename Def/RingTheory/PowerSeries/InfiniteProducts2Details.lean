/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts2.Part6
import Abbrev.RingTheory.PowerSeries.InfiniteProducts2Details
open scoped Polynomial BigOperators

/-!
# Infinite Products of Formal Power Series - Part 2

This file formalizes the second part of the detailed proofs for infinite products
of formal power series, following the Details section of Loehr's "Bijective Combinatorics".

The main content includes:
- Product rules (generalized distributive laws) for infinite products
- Composition rules for infinite products with substitution
- Supporting lemmas about coefficient extraction and summability

## Main Definitions

* `PowerSeries.EssentiallyFinite`: A family `(k_i)_{i ∈ I}` is essentially finite if
  all but finitely many entries equal 0.
* `PowerSeries.SfinI`: The set of essentially finite families in `∏_{i ∈ I} S_i`.

## Main Results

### Product Rules (Generalized Distributive Laws)

* `PowerSeries.prodRule_claim3`: For `(i,k) ∈ S̄ \ T'_n`, we have `[x^m] p_{i,k} = 0`
  for all `m ∈ {0,1,...,n}`. (Claim 3, label: pf.prop.fps.prodrule-fin-inf.Tm-def)
* `PowerSeries.prodRule_claim4`: If `(k_i)_{i ∈ I} ∈ S^I_fin`, then `(p_{i,k_i})_{i ∈ I}`
  is multipliable. (Claim 4)
* `PowerSeries.prodRule_claim5`: Under certain conditions, `[x^n](∏_{i ∈ I} p_{i,k_i}) = 0`.
  (Claim 5)
* `PowerSeries.prodRule_claim6`: For `(k_i) ∈ S^I_fin \ S^I_{I_n}`, the product coefficient
  vanishes. (Claim 6)
* `PowerSeries.prodRule_claim7`: The family `(∏_{i ∈ I} p_{i,k_i})` indexed by essentially
  finite families is summable. (Claim 7)
* `PowerSeries.prodRule_claim8`: Coefficient reduction to finite index sets. (Claim 8)
* `PowerSeries.prodRule_claim9`: Coefficient vanishing for non-contributing terms. (Claim 9)
* `PowerSeries.prodRule_claim10`: Product reduction to finite index sets. (Claim 10)
* `PowerSeries.prodRule_claim11`: Finite product-sum interchange. (Claim 11)
* `PowerSeries.prodRule_infInf`: **Main Proposition** (prop.fps.prodrule-inf-inf) - The
  generalized distributive law for infinite products and infinite sums:
  `∏_{i ∈ I} ∑_{k ∈ S_i} p_{i,k} = ∑_{(k_i) ∈ S^I_fin} ∏_{i ∈ I} p_{i,k_i}`

### Composition Rules

* `PowerSeries.comp_prod_finite`: For finite `I`, `(∏_{i ∈ I} f_i) ∘ g = ∏_{i ∈ I} (f_i ∘ g)`.
  (Lemma lem.fps.subs.rule-infprod-fin)
* `PowerSeries.comp_prod_multipliable`: If `(f_i)_{i ∈ I}` is multipliable and `[x^0]g = 0`,
  then `(f_i ∘ g)_{i ∈ I}` is multipliable. (Proposition prop.fps.subs.rule-infprod, part 1)
* `PowerSeries.comp_prod_infinite`: For multipliable `(f_i)_{i ∈ I}` with `[x^0]g = 0`,
  `(∏_{i ∈ I} f_i) ∘ g = ∏_{i ∈ I} (f_i ∘ g)`. (Proposition prop.fps.subs.rule-infprod, part 2)

## References

* [Loehr, *Bijective Combinatorics*, Details: Infinite Products (Part 2)]
-/


namespace PowerSeries

variable {K : Type*} [CommRing K]

/-!
### Summability and Multipliability for Product Rules

The following definitions and lemmas support the product rule proofs.
-/


/-- For a summable family `(p_{i,k})`, the set `T_m` of pairs `(i,k)` with nonzero
`[x^m] p_{i,k}` is finite. This corresponds to equation (pf.prop.fps.prodrule-fin-inf.Tm-def).
(label: pf.prop.fps.prodrule-fin-inf.Tm-def) -/
def CoeffSupportSet {I : Type*} (p : I → ℕ → PowerSeries K) (m : ℕ) : Set (I × ℕ) :=
  {ik : I × ℕ | ik.2 ≠ 0 ∧ coeff m (p ik.1 ik.2) ≠ 0}

/-- The union of coefficient support sets up to degree n.
This corresponds to `T'_n = T_0 ∪ T_1 ∪ ... ∪ T_n`. -/
def CoeffSupportSetUnion {I : Type*} (p : I → ℕ → PowerSeries K) (n : ℕ) : Set (I × ℕ) :=
  ⋃ m ∈ Finset.range (n + 1), CoeffSupportSet p m

/-- The index set `I_n` of first components appearing in `T'_n`. -/
def IndexSetIn {I : Type*} (p : I → ℕ → PowerSeries K) (n : ℕ) : Set I :=
  {i : I | ∃ k, (i, k) ∈ CoeffSupportSetUnion p n}

/-- The value set `K_n` of second components appearing in `T'_n`. -/
def ValueSetKn {I : Type*} (p : I → ℕ → PowerSeries K) (n : ℕ) : Set ℕ :=
  {k : ℕ | ∃ i, (i, k) ∈ CoeffSupportSetUnion p n}

/-!
### Claim 3: Coefficient Vanishing Outside T'_n

For `(i,k) ∈ S̄ \ T'_n`, we have `[x^m] p_{i,k} = 0` for all `m ∈ {0,1,...,n}`.
(label: pf.prop.fps.prodrule-fin-inf.Tm-def)
-/
/-!
### Claim 4: Multipliability of Product Families

If `(k_i)_{i ∈ I}` is essentially finite, then `(p_{i,k_i})_{i ∈ I}` is multipliable.
-/
/-!
### Claim 5: Product Coefficient Vanishing

Under certain conditions on the index family, the product coefficient vanishes.
-/
/-!
### Claim 6: Product Coefficient Vanishing for Non-Contributing Families

For families outside `S^I_{I_n}`, the product coefficient vanishes.
-/
/-!
### Claim 7: Summability of Product Family

The family `(∏_{i ∈ I} p_{i,k_i})` indexed by essentially finite `(k_i)` is summable.
-/
/-!
### Claim 8: Coefficient Reduction to Finite Index Sets

The coefficient of the sum over essentially finite families equals
the coefficient of the sum over a finite index set.
-/


/-- Extend a function from a finite subset to the full type by setting values to 0 outside. -/
def extendFromFinset {I : Type*} [DecidableEq I] (In : Finset I) (f : (i : In) → ℕ) : I → ℕ :=
  fun i => if h : i ∈ In then f ⟨i, h⟩ else 0

/-- Restrict a function to a finite subset. -/
def restrictToFinset {I : Type*} (In : Finset I) (k : I → ℕ) : (i : In) → ℕ :=
  fun i => k i.1

/-!
### Claim 9: Sum Coefficient Vanishing

For `i ∉ I_n`, the sum `∑_{k ∈ S_i \ {0}} p_{i,k}` has vanishing coefficients
up to degree `n`.
-/
/-!
### Claim 10: Product Reduction to Finite Index Sets

The product over `I` reduces to the product over `I_n` for coefficient extraction.
-/
/-!
### Claim 11: Finite Product-Sum Interchange

For a finite index set, the product of sums equals the sum of products.
-/
/-!
### Main Proposition: Infinite-Infinite Product Rule (Generalized Distributive Law)

This is the culmination of Claims 3-11. It states that for a summable family
`(p_{i,k})` with `p_{i,0} = 1`, the infinite product of infinite sums equals
the sum over essentially finite families of products.

Proposition prop.fps.prodrule-inf-inf:
`∏_{i ∈ I} ∑_{k ∈ S_i} p_{i,k} = ∑_{(k_i)_{i ∈ I} ∈ S^I_fin} ∏_{i ∈ I} p_{i,k_i}`
-/


/-- The set `S^I_fin` of essentially finite families in `∏_{i ∈ I} S_i`. -/
def SfinI {I : Type*} (S : I → Set ℕ) : Set (I → ℕ) :=
  {k : I → ℕ | (∀ i, k i ∈ S i) ∧ EssentiallyFinite k}

/-!
### Composition Rules for Infinite Products

The following results establish that composition distributes over infinite products.
-/
/-!
### Additional Supporting Lemmas
-/

end PowerSeries
