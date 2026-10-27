/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors:
-/
import Mathlib
import Theorem.RingTheory.PowerSeries.InfiniteProducts2.Part3
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

section InfiniteProductRules

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

section ExtensionRestriction

variable {I : Type*} {S : I → Type*} [∀ i, Zero (S i)]

/-- Package the extension as a subtype of essentially finite functions. -/
def extendToI_subtype {I_n : Set I} (hI_n_finite : I_n.Finite)
    (f : (i : hI_n_finite.toFinset) → S i) :
    { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 } :=
  ⟨extendToI hI_n_finite f, extendToI_essentiallyFinite hI_n_finite f⟩

/-- Restriction map: restrict an essentially finite function on I to a finite subset I_n. -/
def restrictToI_n {I_n : Set I} (hI_n_finite : I_n.Finite)
    (f : { f : (i : I) → S i // ∀ᶠ i in Filter.cofinite, f i = 0 }) :
    (i : hI_n_finite.toFinset) → S i :=
  fun ⟨i, _⟩ => f.val i

end ExtensionRestriction

/-- The set `S̄` from Proposition prop.fps.prodrule-inf-infN: pairs `(i, k)` where
`i ∈ {1, 2, 3, ...}`, `k ∈ S_i`, and `k ≠ 0`. -/
def SBar (S : ℕ+ → Type*) [∀ i, Zero (S i)] : Type _ :=
  Σ i : ℕ+, { k : S i // k ≠ 0 }

end InfiniteProductRules

/-! ## Lemma on Irrelevance of High-Order Terms

This lemma is used in the proof of the infinite product rule.
-/


section IrrelevanceLemma

open scoped PowerSeries.WithPiTopology

open Filter Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

end IrrelevanceLemma

/-! ## Euler's Identity for Odd Parts

A beautiful application of the product rules.
-/


section EulerIdentity

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [NoZeroDivisors K]

/-- Equivalence between positive odd natural numbers and positive natural numbers.
    Maps n ↦ (n+1)/2 with inverse i ↦ 2i-1. -/
def oddPNatEquivPNat : { n : ℕ+ // Odd (n : ℕ) } ≃ ℕ+ where
  toFun n := ⟨((n : ℕ) + 1) / 2, by
    rcases n.prop with ⟨k, hk⟩
    have : ((n : ℕ) + 1) / 2 = k + 1 := by omega
    rw [this]; exact Nat.succ_pos k⟩
  invFun i := ⟨⟨2 * i - 1, by have := i.pos; omega⟩, by
    simp only [PNat.mk_coe]
    have h : 1 ≤ 2 * (i : ℕ) := by have := i.pos; omega
    rw [Nat.odd_sub h]; simp⟩
  left_inv n := by
    apply Subtype.ext; apply Subtype.ext
    simp only [PNat.mk_coe]
    rcases n.prop with ⟨k, hk⟩
    have hdiv : (2 : ℕ) ∣ ((n : ℕ) + 1) := ⟨k + 1, by omega⟩
    have h3 : 2 * (((n : ℕ) + 1) / 2) = (n : ℕ) + 1 := Nat.mul_div_cancel' hdiv
    have hpos : 1 ≤ (n : ℕ) := n.val.pos
    have h4 : 2 * (((n : ℕ) + 1) / 2) - 1 = (n : ℕ) := by omega
    exact h4
  right_inv i := by
    apply Subtype.ext
    simp only [PNat.mk_coe]
    have hi := i.pos
    have h1 : (2 * (i : ℕ) - 1 + 1) / 2 = i := by omega
    exact h1

/-- Bijection between `ℕ+` and `{i : ℕ | Odd (i+1)}`.
Maps `j ↦ 2j - 2` so that `(2j-2) + 1 = 2j - 1` is odd. -/
def pnatEquivEvenNat : ℕ+ ≃ {i : ℕ | Odd (i + 1)} where
  toFun j := ⟨2 * j - 2, by
    have hj := j.pos
    simp only [Set.mem_ofPred_eq]
    have h : 2 * (j : ℕ) - 2 + 1 = 2 * j - 1 := by omega
    rw [h]
    have h2 : 1 ≤ 2 * (j : ℕ) := by omega
    rw [Nat.odd_sub h2]
    simp⟩
  invFun i := ⟨(i.val + 2) / 2, by
    have hi := i.prop
    simp only [Set.mem_ofPred_eq] at hi
    obtain ⟨k, hk⟩ := hi
    have h : (i.val + 2) / 2 = k + 1 := by omega
    rw [h]
    exact Nat.succ_pos k⟩
  left_inv j := by
    apply Subtype.ext
    have hj := j.pos
    have h2 : (2 * (j : ℕ) - 2 + 2) / 2 = j := by omega
    exact h2
  right_inv i := by
    apply Subtype.ext
    have hi := i.prop
    simp only [Set.mem_ofPred_eq] at hi
    obtain ⟨k, hk⟩ := hi
    simp only [PNat.mk_coe]
    omega

end EulerIdentity

/-! ## Combinatorial Interpretation: Partitions

The combinatorial consequence of Euler's identity.
-/


section Partitions

/-- Number of ways to write `n` as a sum of distinct positive integers. -/
def numDistinctPartitions (n : ℕ) : ℕ :=
  (Nat.Partition.distincts n).card

/-- Number of ways to write `n` as a sum of odd positive integers. -/
def numOddPartitions (n : ℕ) : ℕ :=
  (Nat.Partition.odds n).card

/-! ## Infinite Products and Substitution

The substitution rule extends to infinite products.
-/


/-! ## Exponentials, Logarithms and Infinite Products

The Exp and Log maps convert between infinite sums and products.
These results require K to be a ℚ-algebra for the formal exp and log to be defined.

**Note on formalization status:**

The source material (Propositions prop.fps.Exp-Log-infsum and prop.fps.Exp-Log-infprod) states:
- `Exp(∑_{i ∈ I} f_i) = ∏_{i ∈ I} Exp(f_i)` for summable families in `K⟦X⟧_0`
- `Log(∏_{i ∈ I} f_i) = ∑_{i ∈ I} Log(f_i)` for multipliable families in `K⟦X⟧_1`

These require:
1. A general composition/substitution operation for power series (to define `Exp(f)` for `f` with
   zero constant term)
2. A formal logarithm `Log : K⟦X⟧_1 → K⟦X⟧_0` (not yet in Mathlib)

The finite versions use `PowerSeries.exp_mul_exp_eq_exp_add`: `exp(aX) * exp(bX) = exp((a+b)X)`.
Once the infrastructure is available, the infinite versions should follow by taking limits.
-/
/-! ## Exp/Log Placeholder Section

The source material includes Propositions `prop.fps.Exp-Log-infsum` and `prop.fps.Exp-Log-infprod`
relating infinite sums/products via Exp and Log maps.

**Canonical definitions for FPS with constant term 0 or 1:**
- `PowerSeries.PowerSeries₀` (FPS with constant term 0) — see `FPS/ExpLog.lean`
- `PowerSeries.PowerSeries₁` (FPS with constant term 1) — see `FPS/ExpLog.lean`

These definitions have extensive API including:
- `PowerSeries₀.addSubgroup` — additive subgroup structure
- `PowerSeries₁.subgroup` — multiplicative subgroup structure (for fields)
- Membership lemmas (`mem_PowerSeries₀_iff`, `mem_PowerSeries₁_iff`)
- Closure properties (`add_mem`, `mul_mem`, `inv_mem`, etc.)
- Composition lemmas (`subst_mem`, `exp_subst_mem_PowerSeries₁`, etc.)
- The `Exp` and `Log` maps between these sets

Once the Exp/Log infrastructure from `ExpLog.lean` is integrated, the infinite versions
(`prop.fps.Exp-Log-infsum` and `prop.fps.Exp-Log-infprod`) can be formalized by taking limits.
-/
/-! ## The Binary Product Rule (eq.fps.prod.binary.prod-inf)

The special case that motivated the general theory.
-/


end Partitions
end
