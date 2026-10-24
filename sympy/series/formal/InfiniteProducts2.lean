/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors:
-/
import Mathlib
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


open scoped Polynomial
open Finset PowerSeries

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

namespace EssentiallyFinite

variable {I M : Type*} [Zero M]
/-! ### Basic Properties -/


/-- The zero function is essentially finite. -/
theorem zero : EssentiallyFinite (0 : I → M) := by
  simp only [EssentiallyFinite, Function.support_zero, Set.finite_empty]
/-! ### Characterization via Filter.cofinite -/
/-! ### Operations on Essentially Finite Families -/


section AddGroup
variable {M : Type*} [AddGroup M]

end AddGroup

section Ring
variable {R : Type*} [Ring R] [NoZeroDivisors R]

end Ring
/-! ### Finset and Finsupp Operations -/


/-- Convert an essentially finite family to a Finsupp. -/
noncomputable def toFinsupp {f : I → M} (hf : EssentiallyFinite f) : I →₀ M :=
  Finsupp.ofSupportFinite f hf

/-- The support of an essentially finite family as a Finset. -/
noncomputable def supportFinset {f : I → M} (hf : EssentiallyFinite f) : Finset I :=
  hf.toFinset
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
/-! ### Essentially Finite Subtype

The type of essentially finite functions, used in the main product rule theorems. -/


namespace EssentiallyFiniteFamily

variable {I M : Type*} [Zero M]

/-- The underlying function of an essentially finite family. -/
def toFun (f : EssentiallyFiniteFamily I M) : I → M := f.val

instance : CoeFun (EssentiallyFiniteFamily I M) (fun _ => I → M) where
  coe f := f.val

/-- The zero essentially finite family. -/
def zero : EssentiallyFiniteFamily I M := ⟨0, EssentiallyFinite.zero⟩

instance : Zero (EssentiallyFiniteFamily I M) where
  zero := zero

end EssentiallyFiniteFamily
/-! ## Finite Product Rules

These are the basic distributive laws for products of sums.
-/


section FiniteProductRules

variable {L : Type*} [CommSemiring L]

end FiniteProductRules
/-! ## Finite Products of Infinite Sums

Product rules for finite products of infinite (but summable) families.
-/


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

/-- The extension of a function on a finite set is essentially finite. -/
theorem extendToI_essentiallyFinite {I_n : Set I} (hI_n_finite : I_n.Finite)
    (f : (i : hI_n_finite.toFinset) → S i) :
    ∀ᶠ i in Filter.cofinite, extendToI hI_n_finite f i = 0 := by
  classical
  apply Filter.eventually_of_mem (hI_n_finite.toFinset.finite_toSet.compl_mem_cofinite)
  intro i hi
  simp only [extendToI, Set.mem_compl_iff, Finset.mem_coe] at hi ⊢
  exact dite_eq_right hi

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

end Partitions
/-! ## Infinite Products and Substitution

The substitution rule extends to infinite products.
-/


section Substitution

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

end Substitution
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


section BinaryProductRule

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

end BinaryProductRule
