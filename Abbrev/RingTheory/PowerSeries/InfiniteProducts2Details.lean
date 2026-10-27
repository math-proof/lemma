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
### Essentially Finite Families

A family `(k_i)_{i ∈ I}` indexed by a set `I` with values in `ℕ` is essentially finite
if all but finitely many entries equal `0`. This is the key concept for indexing
summable families of products.
-/


/-- A family `f : I → ℕ` is essentially finite if all but finitely many values are 0.
This corresponds to `S^I_fin` in the source.

**This is an alias** for the canonical `_root_.EssentiallyFinite` defined in
`FPS/InfiniteProducts2.lean`. Both definitions are **definitionally equal**:
`{i | f i ≠ 0}.Finite` = `(Function.support f).Finite` by definition.

For the full API (including `_root_.EssentiallyFinite.add`, `_root_.EssentiallyFinite.neg`,
`_root_.EssentiallyFinite.toFinsupp`, etc.), see `FPS/InfiniteProducts2.lean`.

This version is specialized to `ℕ` for use in product rule proofs. -/
abbrev EssentiallyFinite {I : Type*} (f : I → ℕ) : Prop :=
  _root_.EssentiallyFinite f

end PowerSeries
