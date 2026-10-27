/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors:
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts2.Part2
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

namespace EssentiallyFinite

variable {I M : Type*} [Zero M]

/-! ### Examples -/


/-- Example: The sequence (2, 4, 1, 0, 0, 0, ...) is essentially finite. -/
example : EssentiallyFiniteSeq (fun n : ℕ+ =>
    if n = 1 then 2 else if n = 2 then 4 else if n = 3 then 1 else 0) := by
  apply Set.Finite.subset (s := ({1, 2, 3} : Set ℕ+))
  · exact Set.toFinite _
  · intro n hn
    simp only [ne_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Function.mem_support] at *
    by_contra h
    push Not at h
    simp only [h.1, ↓reduceIte, h.2.1, h.2.2, not_true_eq_false] at hn

/-- Example: The alternating sequence (0, 1, 0, 1, 0, 1, ...) is NOT essentially finite. -/
example : ¬ EssentiallyFinite (fun n : ℕ => if n % 2 = 0 then 0 else 1) := by
  intro h
  have hfin : {n : ℕ | n % 2 = 1}.Finite := by
    apply Set.Finite.subset h
    intro n hn
    simp only [Set.mem_ofPred_eq, Function.mem_support] at *
    simp only [hn, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]
  have hinf : {n : ℕ | n % 2 = 1}.Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun n => 2 * n + 1)
    · intro m n hmn
      simp only at hmn
      omega
    · intro n
      simp only [Set.mem_ofPred_eq]
      omega
  exact hinf hfin

end EssentiallyFinite
end
