/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import sympy.combinatorics.qbinomial.QBinomialBasic
/-!
# q-Binomial Formulas

This file formalizes the q-binomial formulas from the Algebraic Combinatorics text,
including:
- The first q-binomial theorem
- The second q-binomial theorem (Potter's binomial theorem)
- Counting subspaces of finite-dimensional vector spaces over finite fields
- Limits of q-binomial coefficients

## Main Definitions (in namespace `AlgebraicCombinatorics.QBinomialRec`)

* `qBinomial`: The q-binomial coefficient `[n choose k]_q`, defined via q-Pascal recurrence
* `qFactorial`: The q-factorial `[n]_q!`
* `qNat`: The q-analog of natural number `[n]_q`

**Namespace structure:** All definitions in this file are in the sub-namespace
`AlgebraicCombinatorics.QBinomialRec` to avoid conflicts with the canonical definitions
in `QBinomialBasic.lean`. The canonical definitions use the monotone function sum formula,
while this file uses the q-Pascal recurrence. Both are equivalent (see `qBinomial_eq_sum_monotone`).

To use definitions from this file:
- Use full path: `AlgebraicCombinatorics.QBinomialRec.qBinomial`
- Or open the namespace: `open AlgebraicCombinatorics.QBinomialRec`

## Main Results

* `qBinomial_eq_sum_monotone`: Equivalence to the monotone function sum definition
* `qBinomial_eq_sum_subsets`: Equivalence to the subset sum formula
* `qBinomial_first_theorem`: The first q-binomial theorem
* `qBinomial_second_theorem`: The second q-binomial theorem (Potter's binomial theorem)
* `qBinomial_subspace_count`: The q-binomial coefficient counts k-dimensional subspaces
* `qBinomial_limit`: The limit of q-binomial coefficients as n → ∞

## References

* Section on q-binomial formulas from Algebraic Combinatorics lecture notes
* See also `QBinomialBasic.lean` for the canonical definition and basic properties
-/


open Polynomial Finset BigOperators

namespace AlgebraicCombinatorics
/-!
## Sub-namespace for Recursive q-Binomial Definitions

The definitions `qNat`, `qFactorial`, `qBinomial`, and related theorems in this file
use the q-Pascal recurrence, which is different from the monotone function sum
definition in `QBinomialBasic.lean`. To avoid namespace conflicts when both files
are imported together, these definitions are placed in the `QBinomialRec` sub-namespace.

The equivalence between the two definitions is proven in `qBinomial_eq_sum_monotone`.

To use these definitions, either:
1. Open the namespace: `open AlgebraicCombinatorics.QBinomialRec`
2. Use the full path: `AlgebraicCombinatorics.QBinomialRec.qBinomial`
-/

namespace QBinomialRec

section QAnalogs
/-!
### Definition def.pars.qbinom.qint: q-integers and q-factorials

This section formalizes the q-analogs of integers and factorials from Definition 2.3.2.

**Part (a)**: The q-integer `[n]_q = q^0 + q^1 + ... + q^{n-1} ∈ ℤ[q]`

**Part (b)**: The q-factorial `[n]_q! = [1]_q · [2]_q · ... · [n]_q ∈ ℤ[q]`

**Part (c)**: For any element `a` of a ring `A`, `[n]_a` and `[n]_a!` denote the results
of substituting `a` for `q` in `[n]_q` and `[n]_q!`, respectively.

### Remark rmk.pars.qbinom.qint.frac

For any `n ∈ ℕ`:
- `[n]_q = (1 - q^n)/(1 - q)` (in ℤ⟦q⟧ or in the field of rational functions)
- `[n]_1 = n`
- `[n]_1! = n!`
-/


variable {R : Type*} [CommRing R]

/-- Definition def.pars.qbinom.qint (a): The q-integer `[n]_q`.

    The q-analog of a natural number is defined as the sum:
    `[n]_q = q^0 + q^1 + q^2 + ... + q^{n-1}`

    This equals `(1 - q^n)/(1 - q)` in appropriate rings (see `qNat_eq_geom_sum`).
    When evaluated at `q = 1`, this equals `n` (see `qNat_at_one`). -/
noncomputable def qNat (q : R) (n : ℕ) : R :=
  ∑ i ∈ range n, q ^ i

/-- Definition def.pars.qbinom.qint (b): The q-factorial `[n]_q!`.

    The q-factorial is defined as the product:
    `[n]_q! = [1]_q · [2]_q · ... · [n]_q`

    When evaluated at `q = 1`, this equals `n!` (see `qFactorial_at_one`). -/
noncomputable def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, qNat q (i + 1)

/-- The q-binomial coefficient (Gaussian binomial coefficient)
    `[n choose k]_q = [n]_q! / ([k]_q! · [n-k]_q!)`.

    This is defined as a polynomial in q with integer coefficients.
    It counts partitions that fit in a k × (n-k) box, weighted by q^|λ|.

    We use the recurrence relation (q-Pascal's identity):
    [n choose k]_q = [n-1 choose k-1]_q + q^k · [n-1 choose k]_q

    This avoids division and works over any commutative ring.

    This definition is equivalent to `AlgebraicCombinatorics.qBinomial` in `QBinomialBasic.lean`,
    which uses the monotone function sum definition. The equivalence is proven in
    `qBinomial_eq_sum_monotone`. The argument order here is `(q : R) (n k : ℕ)` vs
    `(n k : ℕ) (q : R)` in `QBinomialBasic.lean`. -/
noncomputable def qBinomial (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1)
/-!
### Remark rmk.pars.qbinom.qint.frac: Properties of q-integers and q-factorials

The following lemmas formalize the key properties from Remark 2.3.3:
- The geometric series formula: `[n]_q = (1 - q^n)/(1 - q)`
- Evaluation at 1: `[n]_1 = n` and `[n]_1! = n!`
-/
/-!
### Proposition prop.pars.qbinom.alt-defs: Alternative definitions of q-binomial coefficients

This section formalizes the three equivalent characterizations of q-binomial coefficients
from Proposition 11.2.4 (prop.pars.qbinom.alt-defs) of the textbook.

**Part (a)**: Sum over weakly increasing tuples
  `[n choose k]_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ n-k} q^{i₁ + i₂ + ... + i_k}`

**Part (b)**: Sum over k-element subsets
  `[n choose k]_q = ∑_{S ⊆ {1,...,n}, |S| = k} q^{sum(S) - (1 + 2 + ... + k)}`

**Part (c)**: Evaluation at q = 1 gives ordinary binomial coefficient
  `[n choose k]_1 = C(n, k)`

Part (c) is already proved as `qBinomial_at_one` above.
-/


-- Triangular number: 1 + 2 + ... + k
/-- The triangular number T(k) = 1 + 2 + ... + k = k(k+1)/2. -/
def triangular (k : ℕ) : ℕ := k * (k + 1) / 2

-- The set of monotone functions from Fin k to Fin (m + 1)
-- NOTE: We reuse the canonical definition from QBinomialBasic.lean.
-- The definition is copied here (not aliased) to maintain proof compatibility,
-- but it is definitionally equal to `AlgebraicCombinatorics.monotoneFunctions`.
/-- The set of monotone (weakly increasing) functions from Fin k to Fin (m + 1).
    This represents k-tuples (i₁, ..., i_k) with 0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ m.

    This is definitionally equal to `AlgebraicCombinatorics.monotoneFunctions`. -/
def monotoneFunctions (k m : ℕ) : Finset (Fin k → Fin (m + 1)) :=
  Finset.univ.filter fun f => Monotone f

/-- The sum of values of a function from Fin k to Fin (m + 1). -/
def sumValues (k m : ℕ) (f : Fin k → Fin (m + 1)) : ℕ :=
  ∑ i : Fin k, (f i).val

-- The set of k-element subsets of {1, 2, ..., n}
/-- The set of k-element subsets of {1, 2, ..., n}. -/
def kSubsetsOfIcc (n k : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun S => S.card = k)

/-- The sum of elements in a finite set of natural numbers.

    Note: This is named `finsetSumNat` to distinguish from `AlgebraicCombinatorics.CauchyBinet.finsetSumFin`,
    which computes the sum of elements in a `Finset (Fin n)` by extracting their `.val`.
    Both compute "the sum of elements" but for different element types. -/
def finsetSumNat (S : Finset ℕ) : ℕ := S.sum id

/-- Proposition prop.pars.qbinom.alt-defs (a): Alternative definition of q-binomial as sum
    over weakly increasing tuples.

    [n choose k]_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ n-k} q^{i₁ + i₂ + ... + i_k}

    The sum ranges over all weakly increasing k-tuples (i₁, i₂, ..., i_k) with entries in {0, 1, ..., n-k}.
    When k = 0, this is a single term with exponent 0, giving 1.

    **Important**: This theorem requires `k ≤ n`. When k > n, the natural number subtraction
    `n - k = 0` in Lean, so `monotoneFunctions k 0` represents functions `Fin k → Fin 1`,
    which has exactly one element (the constant 0 function). This would give a sum of 1,
    but `qBinomial q n k = 0` when k > n (see `qBinomial_gt`).

    This characterization arises from the bijection between partitions fitting in a k × (n-k) box
    and weakly increasing k-tuples: a partition λ = (λ₁, ..., λ_k) with λ₁ ≤ n-k corresponds to
    the tuple (λ_k, λ_{k-1}, ..., λ₁) (reversed and possibly padded with zeros). -/
-- Helper definitions for the bijections in the proof of qBinomial_eq_sum_monotone
def monotoneFunctionsStartZero (k m : ℕ) : Finset (Fin (k + 1) → Fin (m + 1)) :=
  (monotoneFunctions (k + 1) m).filter fun f => f 0 = 0

def monotoneFunctionsStartPos (k m : ℕ) : Finset (Fin (k + 1) → Fin (m + 1)) :=
  (monotoneFunctions (k + 1) m).filter fun f => f 0 ≠ 0

def dropFirst (k m : ℕ) (f : Fin (k + 1) → Fin (m + 1)) : Fin k → Fin (m + 1) :=
  fun i => f i.succ

def prependZero (k m : ℕ) (g : Fin k → Fin (m + 1)) : Fin (k + 1) → Fin (m + 1) :=
  Fin.cons 0 g

def shiftDown (k m : ℕ) (f : Fin (k + 1) → Fin (m + 2)) (hf : ∀ i, (f i).val ≥ 1) :
    Fin (k + 1) → Fin (m + 1) :=
  fun i => ⟨(f i).val - 1, by have h1 := (f i).isLt; have h2 := hf i; omega⟩

def shiftUp (k m : ℕ) (g : Fin (k + 1) → Fin (m + 1)) : Fin (k + 1) → Fin (m + 2) :=
  fun i => ⟨(g i).val + 1, by have h := (g i).isLt; omega⟩

end QAnalogs
/-!
## Combinatorial Definition of q-Binomial Coefficients (Definition def.pars.qbinom.qbinom)

This section formalizes Definition 4.3.2 from the textbook, which defines the q-binomial
coefficient (Gaussian binomial coefficient) as a sum over partitions:

**(a)** The q-binomial coefficient `[n choose k]_q` is the polynomial
  `∑_{λ} q^|λ|`
where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

**(b)** For any ring element `a`, the evaluation `[n choose k]_a` is obtained by
substituting `a` for `q` in the polynomial `[n choose k]_q`.

### Key Properties

* When k > n, the q-binomial is 0 (empty sum since n - k < 0).
* `[n choose 0]_q = [n choose n]_q = 1` (only the empty partition qualifies).
* When a = 1, we recover the ordinary binomial coefficient: `[n choose k]_1 = C(n,k)`.
-/


section CombinatoricDefinition

/-- A partition has largest part ≤ m if all parts are ≤ m.
    This is used in the combinatorial definition of q-binomial coefficients. -/
def partitionLargestPartLeq {n : ℕ} (p : Nat.Partition n) (m : ℕ) : Prop :=
  ∀ i ∈ p.parts, i ≤ m

/-- A partition has length ≤ k if it has at most k parts.
    This is used in the combinatorial definition of q-binomial coefficients. -/
def partitionLengthLeq {n : ℕ} (p : Nat.Partition n) (k : ℕ) : Prop :=
  p.parts.card ≤ k

instance instDecidablePartitionLargestPartLeq {n m : ℕ} (p : Nat.Partition n) :
    Decidable (partitionLargestPartLeq p m) :=
  inferInstanceAs (Decidable (∀ i ∈ p.parts, i ≤ m))

instance instDecidablePartitionLengthLeq {n k : ℕ} (p : Nat.Partition n) :
    Decidable (partitionLengthLeq p k) :=
  inferInstanceAs (Decidable (p.parts.card ≤ k))

/-- The set of partitions of a given size that fit in a k × m box
    (i.e., have length ≤ k and largest part ≤ m).

    For the q-binomial `[n choose k]_q`, we use m = n - k.

    **Argument order:** `(size k m : ℕ)` where:
    - `size` is the partition size
    - `k` is the maximum number of parts (length ≤ k)
    - `m` is the maximum part size (largest part ≤ m)

    This matches the convention in `AlgebraicCombinatorics.partitionsInBox` from `QBinomialBasic.lean`. -/
def partitionsInBox (size k m : ℕ) : Finset (Nat.Partition size) :=
  (Finset.univ : Finset (Nat.Partition size)).filter
    (fun p => partitionLengthLeq p k ∧ partitionLargestPartLeq p m)

/-- The count of partitions of a given size that fit in a k × m box. -/
def countPartitionsInBox (size k m : ℕ) : ℕ := (partitionsInBox size k m).card

/-- Partitions with exactly k parts (not just at most k parts), fitting in a box with largest part ≤ m.
    Used in the q-Pascal identity proof to split partitions by exact number of parts. -/
def partitionsInBoxExact (size k m : ℕ) : Finset (Nat.Partition size) :=
  (Finset.univ : Finset (Nat.Partition size)).filter
    (fun p => p.parts.card = k ∧ partitionLargestPartLeq p m)

instance instDecidablePartitionsInBoxExact {size k m : ℕ} (p : Nat.Partition size) :
    Decidable (p.parts.card = k ∧ partitionLargestPartLeq p m) :=
  inferInstanceAs (Decidable (p.parts.card = k ∧ (∀ i ∈ p.parts, i ≤ m)))

/-- Helper: sum of a multiset is ≥ its cardinality when all elements are ≥ 1. -/
theorem multiset_sum_ge_card {m : Multiset ℕ} (h : ∀ x ∈ m, x ≥ 1) : m.sum ≥ m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    have ha : a ≥ 1 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≥ 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    specialize ih hs
    omega

/-- Helper: sum of (x - 1) over a multiset equals sum - card when all elements are ≥ 1. -/
theorem multiset_sum_sub_one (m : Multiset ℕ) (h : ∀ x ∈ m, x ≥ 1) :
    (m.map (· - 1)).sum = m.sum - m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : a ≥ 1 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≥ 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have ihs := ih hs
    have hsum_ge : s.sum ≥ s.card := multiset_sum_ge_card hs
    omega

/-- Forward bijection for q-Pascal: subtract 1 from each part of a partition with exactly k+1 parts.
    Uses `Nat.Partition.ofSums` to filter out zeros. -/
noncomputable def subtractOnePartition (s k m : ℕ) (p : Nat.Partition s)
    (hp : p ∈ partitionsInBoxExact s (k + 1) m) : Nat.Partition (s - (k + 1)) := by
  have hparts : p.parts.card = k + 1 := by
    simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and] at hp
    exact hp.1
  have hpos : ∀ x ∈ p.parts, x ≥ 1 := fun x hx => p.parts_pos hx
  let newParts := p.parts.map (· - 1)
  have hsum : newParts.sum = s - (k + 1) := by
    simp only [newParts]
    rw [multiset_sum_sub_one p.parts hpos, p.parts_sum, hparts]
  exact Nat.Partition.ofSums (s - (k + 1)) newParts hsum

/-- Inverse bijection for q-Pascal: add 1 to each part and pad with 1s to get exactly k+1 parts. -/
noncomputable def addOnePartition (t k m : ℕ) (q : Nat.Partition t)
    (hq : q ∈ partitionsInBox t (k + 1) (m - 1)) : Nat.Partition (t + (k + 1)) := by
  have hlen : q.parts.card ≤ k + 1 := by
    simp only [partitionsInBox, mem_filter, mem_univ, true_and] at hq
    simp only [partitionLengthLeq] at hq
    exact hq.1
  let addedParts := q.parts.map (· + 1)
  let extraOnes := Multiset.replicate (k + 1 - q.parts.card) 1
  let newParts := addedParts + extraOnes
  have hsum : newParts.sum = t + (k + 1) := by
    simp only [newParts, addedParts, extraOnes]
    simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
    have h1 : (q.parts.map (· + 1)).sum = q.parts.sum + q.parts.card := by
      induction q.parts using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        omega
    rw [h1, q.parts_sum]
    omega
  have hpos : ∀ i ∈ newParts, 0 < i := by
    intro i hi
    simp only [newParts, addedParts, extraOnes, Multiset.mem_add] at hi
    rcases hi with hi_add | hi_extra
    · simp only [Multiset.mem_map] at hi_add
      obtain ⟨j, _, hj_eq⟩ := hi_add
      omega
    · simp only [Multiset.mem_replicate] at hi_extra
      omega
  exact ⟨newParts, @hpos, hsum⟩

/-- The q-binomial coefficient as a polynomial in ℤ[q].
    (Definition def.pars.qbinom.qbinom (a))

    `[n choose k]_q = ∑_{λ} q^|λ|`

    where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

    This is a polynomial (not just a formal power series) because there are
    finitely many such partitions - they all fit in a k × (n-k) box, so their
    size is at most k · (n-k).

    When k > n, this is 0 (the empty sum, since n - k < 0 means no partitions qualify). -/
noncomputable def qBinomialPolyDef (n k : ℕ) : Polynomial ℤ :=
  if k ≤ n then
    ∑ size ∈ range (k * (n - k) + 1),
      (countPartitionsInBox size k (n - k)) • (Polynomial.X : Polynomial ℤ) ^ size
  else 0

variable {R : Type*} [CommRing R]

/-- The q-binomial coefficient evaluated at a ring element.
    (Definition def.pars.qbinom.qbinom (b))

    `[n choose k]_a = ∑_{λ} a^|λ|`

    where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

    This is the result of substituting `a` for `q` in the polynomial `[n choose k]_q`. -/
noncomputable def qBinomialEval (n k : ℕ) (a : R) : R :=
  (qBinomialPolyDef n k).eval₂ (Int.castRingHom R) a

/-- Alternative definition: directly sum over partitions. -/
def qBinomialEvalDirect (n k : ℕ) (a : R) : R :=
  if k ≤ n then
    ∑ size ∈ range (k * (n - k) + 1),
      (countPartitionsInBox size k (n - k)) • a ^ size
  else 0

end CombinatoricDefinition

section ProductRule

variable {L : Type*} [CommRing L]

end ProductRule

section FirstQBinomialTheorem

variable {K : Type*} [CommRing K]

end FirstQBinomialTheorem

section SecondQBinomialTheorem

variable {L : Type*} [CommRing L]
variable {A : Type*} [Ring A] [Algebra L A]

/-- Example: For 2×2 matrices with ba = -ab, the second q-binomial theorem applies with ω = -1. -/
example : ∃ (a b : Matrix (Fin 2) (Fin 2) ℤ), b * a = (-1 : ℤ) • (a * b) := by
  use !![0, 1; 1, 0], !![1, 0; 0, -1]
  native_decide

end SecondQBinomialTheorem

section LinearIndependence

variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [Module F V]

end LinearIndependence

section CountingSubspaces

variable {F : Type*} [Field F] [Fintype F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- The span map sends a linearly independent k-tuple to its span (a k-dimensional subspace). -/
noncomputable def spanMap (k : ℕ) :
    {v : Fin k → V // LinearIndependent F v} → {W : Submodule F V // Module.finrank F W = k} :=
  fun ⟨v, hv⟩ => ⟨Submodule.span F (Set.range v), by
    rw [finrank_span_eq_card hv, Fintype.card_fin]⟩

-- Helper lemma: v maps into W when span(v) = W
omit [Fintype F] [Module.Finite F V] in
theorem mem_of_spanMap_eq {k : ℕ} {v : Fin k → V}
    {W : Submodule F V} (hW : Submodule.span F (Set.range v) = W) (i : Fin k) : v i ∈ W := by
  rw [← hW]
  exact Submodule.subset_span (Set.mem_range_self i)

-- Bijection between {v : Fin k → W // LinearIndependent F (Subtype.val ∘ v)} and
-- {v : Fin k → W // LinearIndependent F v}
private noncomputable def linIndepEquiv (k : ℕ) (W : Submodule F V) :
    {v : Fin k → W // LinearIndependent F (Subtype.val ∘ v)} ≃
    {v : Fin k → W // LinearIndependent F v} := by
  refine Equiv.subtypeEquiv (Equiv.refl _) ?_
  intro v
  constructor
  · intro h
    exact LinearIndependent.of_comp W.subtype h
  · intro h
    exact h.map' W.subtype (Submodule.ker_subtype W)

-- Bijection between fiber and lin indep k-tuples in W
noncomputable def fiberEquiv (k : ℕ) (W : {W : Submodule F V // Module.finrank F W = k}) :
    {v : {v : Fin k → V // LinearIndependent F v} // spanMap k v = W} ≃
    {v : Fin k → W.val // LinearIndependent F v} := by
  refine (Equiv.ofBijective ?_ ⟨?_, ?_⟩).trans (linIndepEquiv k W.val)
  -- Forward map: given v with span(v) = W, restrict to W
  · intro ⟨⟨v, hv⟩, hvW⟩
    have heq : Submodule.span F (Set.range v) = W.val := by
      simp only [spanMap, Subtype.ext_iff] at hvW
      exact hvW
    refine ⟨fun i => ⟨v i, mem_of_spanMap_eq heq i⟩, ?_⟩
    simp only [Function.comp_def]
    exact hv
  -- Injective
  · intro ⟨⟨v1, hv1⟩, hvW1⟩ ⟨⟨v2, hv2⟩, hvW2⟩ heq
    simp only [Subtype.mk.injEq] at heq ⊢
    funext i
    have := congrFun heq i
    simp only [Subtype.mk.injEq] at this
    exact this
  -- Surjective
  · intro ⟨w, hw⟩
    let v : Fin k → V := Subtype.val ∘ w
    have hv : LinearIndependent F v := hw
    have hspan : Submodule.span F (Set.range v) = W.val := by
      have hle : Submodule.span F (Set.range v) ≤ W.val := by
        apply Submodule.span_le.mpr
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact (w i).prop
      have hfinrank : Module.finrank F (Submodule.span F (Set.range v)) = k := by
        rw [finrank_span_eq_card hv, Fintype.card_fin]
      exact Submodule.eq_of_le_of_finrank_eq hle (hfinrank.trans W.prop.symm)
    refine ⟨⟨⟨v, hv⟩, ?_⟩, ?_⟩
    · simp only [spanMap, Subtype.ext_iff]
      exact hspan
    · simp only [Subtype.mk.injEq]
      ext i
      simp [v]

end CountingSubspaces

section Limits

/-- The number of partitions of n with at most k parts. -/
noncomputable def partitionCountAtMostKParts (n k : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition n // p.parts.card ≤ k}

open scoped PowerSeries.WithPiTopology

/-- The bijection between partitions with all parts ≤ k and partitions with at most k parts.

    This is a well-known combinatorial fact: the two sets are in bijection via
    Young diagram conjugation (transpose).

    For a partition p with parts [p₁, p₂, ..., pₘ] (sorted decreasing):
    - The conjugate partition has its i-th part equal to #{j : pⱼ ≥ i}
    - This is an involution that swaps "max part" with "number of parts"

    Key properties:
    - If all parts of p are ≤ k, then the conjugate has at most k parts
    - If p has at most k parts, then the conjugate has all parts ≤ k

    The proof uses YoungDiagram.transpose from Mathlib, which provides the conjugation
    operation on Young diagrams. -/
-- Helper: Young diagram card equals sum of row lengths
theorem youngDiagram_card_eq_rowLens_sum (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  simp only [YoungDiagram.card, YoungDiagram.rowLens]
  have hsum : (List.map μ.rowLen (List.range (μ.colLen 0))).sum =
              ∑ i ∈ range (μ.colLen 0), μ.rowLen i := by
    induction μ.colLen 0 with
    | zero => simp
    | succ m ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
                 List.sum_singleton, sum_range_succ]
      rw [ih]
  rw [hsum]
  conv_rhs => arg 2; ext i; rw [YoungDiagram.rowLen_eq_card]
  have hcells : μ.cells = (range (μ.colLen 0)).biUnion (fun i => μ.row i) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_biUnion, mem_range, YoungDiagram.mem_cells, YoungDiagram.mem_row_iff]
    constructor
    · intro hcell
      have hi : i < μ.colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen]
        exact μ.up_left_mem (le_refl i) (Nat.zero_le j) hcell
      exact ⟨i, hi, hcell, rfl⟩
    · intro ⟨i', hi', hcell, heq⟩
      exact heq ▸ hcell
  rw [hcells, Finset.card_biUnion]
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_iff_ne]
  intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
  simp only [YoungDiagram.mem_row_iff] at ha hc
  cases heq
  exact hij (ha.2.symm.trans hc.2)

-- Helper: ofRowLens card equals list sum
theorem ofRowLens_card_eq_sum (w : List ℕ) (hw : w.SortedGE) (hpos : ∀ x ∈ w, 0 < x) :
    (YoungDiagram.ofRowLens w hw).card = w.sum := by
  rw [youngDiagram_card_eq_rowLens_sum, YoungDiagram.rowLens_ofRowLens_eq_self hpos]

-- Helper: positivity of sorted parts
theorem parts_sort_pos' (m : ℕ) (p : Nat.Partition m) :
    ∀ x ∈ p.parts.sort (· ≥ ·), 0 < x := by
  intro x hx
  have : x ∈ p.parts := by simp only [Multiset.mem_sort] at hx; exact hx
  exact p.parts_pos this

-- Helper: sortedness of sorted parts
theorem parts_sort_sorted' (m : ℕ) (p : Nat.Partition m) :
    (p.parts.sort (· ≥ ·)).SortedGE :=
  (Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE

-- Helper: transpose preserves card
theorem transpose_card' (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  simp only [YoungDiagram.card]
  have h : μ.transpose.cells = (Equiv.prodComm ℕ ℕ).finsetCongr μ.cells := rfl
  rw [h, Equiv.finsetCongr_apply, Finset.card_map]

-- Define the Young diagram for a partition
noncomputable def partitionToYoungDiagram' (m : ℕ) (p : Nat.Partition m) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (parts_sort_sorted' m p)

-- The Young diagram has card m
theorem partitionToYoungDiagram_card' (m : ℕ) (p : Nat.Partition m) :
    (partitionToYoungDiagram' m p).card = m := by
  unfold partitionToYoungDiagram'
  rw [ofRowLens_card_eq_sum _ _ (parts_sort_pos' m p)]
  have hsort : (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ) = p.parts := Multiset.sort_eq p.parts (· ≥ ·)
  calc (p.parts.sort (· ≥ ·)).sum
      = (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ).sum := rfl
    _ = p.parts.sum := by rw [hsort]
    _ = m := p.parts_sum

-- Define the conjugate partition
noncomputable def conjugatePartition' (m : ℕ) (p : Nat.Partition m) : Nat.Partition m := by
  let μ := partitionToYoungDiagram' m p
  have hcard : μ.transpose.card = m := by rw [transpose_card', partitionToYoungDiagram_card']
  have hsum : μ.transpose.rowLens.sum = m := by rw [← youngDiagram_card_eq_rowLens_sum, hcard]
  exact ⟨μ.transpose.rowLens, fun hi => μ.transpose.pos_of_mem_rowLens _ hi,
         by rw [Multiset.sum_coe]; exact hsum⟩

end Limits

end QBinomialRec

end AlgebraicCombinatorics
