/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors:
-/
import Mathlib
import Instance.RingTheory.PowerSeries.InfiniteProducts2.Part2
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

section FiniteProductInfiniteSums

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-- Equivalence between `S (last n) × ((i : Fin n) → S (castSucc i))` and `(i : Fin (n+1)) → S i`.
This is used in the inductive proof of the finite product rule. -/
def finSuccProdEquiv (n : ℕ) (S : Fin (n + 1) → Type*) :
    S (Fin.last n) × ((i : Fin n) → S (Fin.castSucc i)) ≃ ((i : Fin (n + 1)) → S i) :=
  ⟨fun ⟨a, f⟩ => Fin.lastCases a f,
   fun g => ⟨g (Fin.last n), fun i => g (Fin.castSucc i)⟩,
   fun ⟨a, f⟩ => by simp only [Fin.lastCases_last, Fin.lastCases_castSucc],
   fun g => by ext i; refine Fin.lastCases (by simp) (fun j => by simp) i⟩

end FiniteProductInfiniteSums

/-! ## Infinite Product Rules

The main results: product rules for infinite products of sums.
-/


section InfiniteProductRules

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-! ### Technical Helper Lemmas

These lemmas are used in the proof of summability for the RHS of the infinite product rule.
-/
/-! ### Helper Lemmas for the General Infinite Product Rule

These lemmas correspond to the claims in the detailed proof of Proposition prop.fps.prodrule-inf-inf.
-/

end InfiniteProductRules

section SummableFiberComplete

/-! ### Summable Fiber Lemma (Complete Space Version)

This section proves that fibers of summable families are summable when the coefficient
ring K is a complete uniform space. This is stronger than the discrete case but requires
completeness.
-/


open scoped PowerSeries.WithPiTopology

variable [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K] [CompleteSpace K]

end SummableFiberComplete

section InfiniteProductRules

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-! ### Helper Lemmas for Coefficient Computation

The following lemmas implement the key insight from the tex proof (Claims 9-10):
factors with high order don't affect low-degree coefficients, allowing us to
reduce infinite products to finite products when computing specific coefficients.
-/


section HelperLemmas

open Filter Topology

end HelperLemmas

/-! ### Extension and Restriction Maps for Bijection

These helper lemmas establish the bijection between functions on a finite subset I_n
and essentially finite functions on the full index set I. This bijection is key to
proving the infinite product rule.
-/


section ExtensionRestriction

variable {I : Type*} {S : I → Type*} [∀ i, Zero (S i)]

/-- Extension map: extend a function on a finite subset I_n to all of I by setting 0 outside.
This is used to establish the bijection in the infinite product rule. -/
def extendToI {I_n : Set I} (hI_n_finite : I_n.Finite)
    (f : (i : hI_n_finite.toFinset) → S i) : (i : I) → S i := by
  classical
  exact fun i => if h : i ∈ hI_n_finite.toFinset then f ⟨i, h⟩ else 0

end ExtensionRestriction
end InfiniteProductRules
end
