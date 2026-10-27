/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors:
-/
import Mathlib
open scoped Polynomial
open Finset PowerSeries

/-!
# Product Rules (Generalized Distributive Laws) for Infinite Products

This file formalizes the product rules for expanding products of sums, both finite and infinite,
following the treatment in the AlgebraicCombinatorics book.

## Main definitions

* `EssentiallyFinite`: A family `(k_i)_{i ∈ I}` is essentially finite if all but finitely many
  `i ∈ I` satisfy `k_i = 0`. This is used to describe which terms appear when expanding
  infinite products of sums.

## Main results

### Finite Product Rules
* `prod_sum_eq_sum_prod_finset`: (Proposition prop.fps.prodrule-fin-fin) A finite product of
  finite sums equals a sum over the Cartesian product of the index sets.
* `prod_tsum_eq_tsum_prod_finset`: (Proposition prop.fps.prodrule-fin-inf) A finite product of
  infinite summable families equals a sum over the Cartesian product.

### Infinite Product Rules
* `tprod_tsum_eq_tsum_prod_essentiallyFinite_nat`: (Proposition prop.fps.prodrule-inf-infN)
  An infinite product of sums (indexed by positive integers) equals a sum over essentially
  finite sequences.
* `tprod_tsum_eq_tsum_prod_essentiallyFinite`: (Proposition prop.fps.prodrule-inf-inf)
  General version with arbitrary index set `I`.

### Applications
* `euler_odd_parts_identity`: (Proposition prop.gf.prod.euler-odd) Euler's identity:
  `∏_{i>0} (1 - x^{2i-1})⁻¹ = ∏_{k>0} (1 + x^k)`
* `euler_distinct_odd_partitions`: (Theorem thm.gf.prod.euler-comb) The number of partitions
  of `n` into distinct parts equals the number of partitions into odd parts.

### Substitution
* `tprod_rescale_substitution`: (Proposition prop.fps.subs.rule-infprod) Infinite products
  commute with rescaling (a special case of substitution).

### Exp/Log
The source material includes Propositions prop.fps.Exp-Log-infsum and prop.fps.Exp-Log-infprod
relating infinite sums/products via Exp and Log maps. The canonical definitions for FPS with
constant term 0 or 1 (`PowerSeries₀` and `PowerSeries₁`) are in `FPS/ExpLog.lean`.

## References

* AlgebraicCombinatorics book, Section on Infinite Products (InfiniteProducts2.tex)
-/


noncomputable section

variable {K : Type*} [CommRing K]

/-! ## Essentially Finite Families

A family `(k_i)_{i ∈ I}` is essentially finite if all but finitely many `i ∈ I` satisfy `k_i = 0`.
This notion is crucial for stating product rules for infinite products.
-/


/-- A family `f : I → M` is essentially finite if all but finitely many values are zero.
This is equivalent to `f` having finite support.

(Definition def.fps.prodrule.ess-fin)

**Canonical definition**: This is the canonical, most general definition of `EssentiallyFinite`.
It is **definitionally equal** to:
- `AlgebraicCombinatorics.FPS.EssentiallyFinite` in `FPSDefinition.lean`
- `PowerSeries.EssentiallyFinite` in `Details/InfiniteProducts2.lean`

All use `{i | f i ≠ 0}.Finite` which equals `(Function.support f).Finite` by definition.
This version has the richest API in the `EssentiallyFinite` namespace. -/
def EssentiallyFinite {I M : Type*} [Zero M] (f : I → M) : Prop :=
  (Function.support f).Finite

/-- A sequence `(k₁, k₂, k₃, ...)` of natural numbers is essentially finite if all but
finitely many terms are zero. -/
def EssentiallyFiniteSeq (k : ℕ+ → ℕ) : Prop :=
  EssentiallyFinite k

/-- The set of essentially finite functions from `I` to `M`. -/
def EssentiallyFiniteFamily (I M : Type*) [Zero M] :=
  { f : I → M // EssentiallyFinite f }

end
