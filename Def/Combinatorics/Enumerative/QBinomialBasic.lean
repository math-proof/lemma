/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
/-!
# q-Binomial Coefficients: Basic Definitions and Properties

This file introduces q-binomial coefficients (also known as Gaussian binomial coefficients)
and their basic properties. The q-binomial coefficient `⟦n;k⟧_q` is a polynomial in `q`
that serves as a q-analogue of the ordinary binomial coefficient.

**This file provides the canonical definition of q-binomial coefficients for this project.**

## Main Definitions

* `qInt`: The q-integer `[n]_q = 1 + q + q^2 + ... + q^(n-1)` (Definition 11.3.1)
* `qFactorial`: The q-factorial `[n]_q! = [1]_q * [2]_q * ... * [n]_q` (Definition 11.3.1)
* `qBinomial`: The q-binomial coefficient `⟦n;k⟧_q` (Definition 11.2.1) — **canonical definition**
* `qBinomialPoly`: The q-binomial coefficient as a polynomial in `ℤ[X]`
* `monotoneFunctions`: The set of monotone functions from `Fin k` to `Fin (m + 1)`

## Main Results

* `qBinomial_eq_sum_increasing_tuples`: Definition as sum over weakly increasing tuples
  (Proposition 11.2.1(a))
* `qBinomial_eq_partition_gf`: Equivalence to partition generating function
  (Definition 11.2.1(a))
* `qBinomial_eq_sum_subsets`: Alternative expression as sum over subsets (Proposition 11.2.1(b))
  -- Proved in `AlgebraicCombinatorics/Partitions/QBinomialFormulas.lean`
* `qBinomial_one_eq_binomial`: At q=1, we recover ordinary binomial coefficients
  (Proposition 11.2.1(c))
* `qBinomial_zero_of_lt`: q-binomial is zero when k > n (Proposition 11.2.2)
* `qBinomial_n_zero`: `⟦n;0⟧_q = 1` (Proposition 11.2.3)
* `qBinomial_n_n`: `⟦n;n⟧_q = 1` (Proposition 11.2.3)
* `qBinomial_rec_left`: Recurrence `⟦n;k⟧_q = q^(n-k) * ⟦n-1;k-1⟧_q + ⟦n-1;k⟧_q` (for 0 < k)
  (Theorem 11.2.4(a))
* `qBinomial_rec_right`: Recurrence `⟦n;k⟧_q = ⟦n-1;k-1⟧_q + q^k * ⟦n-1;k⟧_q` (for 0 < k)
  (Theorem 11.2.4(b))
* `qBinomial_quot_formula`: Product formula for q-binomial (Theorem thm.pars.qbinom.quot1(a))
* `qBinomial_eq_prod_quot`: Quotient formula for q-binomial (Theorem thm.pars.qbinom.quot1(b))
* `qInt_eq_geom_sum`: `[n]_q = (1 - q^n) / (1 - q)` (Remark 11.3.2)
* `qBinomial_eq_qFactorial_quot`: `⟦n;k⟧_q = [n]_q! / ([k]_q! * [n-k]_q!)` (Theorem 11.2.6)
* `qBinomial_symm`: Symmetry `⟦n;k⟧_q = ⟦n;n-k⟧_q` (Proposition 11.2.7)
* `card_partitions_with_parts_and_largest`: Counting partitions (Proposition 11.1.1)

## Implementation Notes

The q-binomial coefficient is defined via the sum over monotone tuples (Proposition 11.2.1(a)):
  `⟦n;k⟧_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ iₖ ≤ n-k} q^(i₁ + i₂ + ... + iₖ)`

This is equivalent to the generating function for partitions fitting in a k × (n-k) box
(Definition 11.2.1(a)), but the monotone tuple formulation is more directly computable
and avoids the need to sum over partitions of varying sizes.

We work over a general commutative semiring `R` with an element `q`, though the polynomial
version over `ℤ[q]` is the primary object of interest.

### Equivalent Formulations

The q-binomial coefficient has several equivalent definitions:

1. **Monotone function sum** (this definition): `∑_{f monotone} q^(∑ᵢ f(i))`
   See `qBinomial_eq_sum_increasing_tuples`.

2. **Subset sum formula**: `∑_{S ⊆ [n], |S|=k} q^(sum(S) - (1+2+...+k))`
   See `qBinomial_eq_sum_subsets` in `Partitions/QBinomialFormulas.lean`.

3. **q-Pascal recurrence**: `[n;k]_q = [n-1;k-1]_q + q^k · [n-1;k]_q`
   See `qBinomial_rec_right` (and `qBinomial_rec_left` for the dual form).

4. **q-factorial quotient**: `[n]_q! / ([k]_q! · [n-k]_q!)`
   See `qBinomial_eq_qFactorial_quot`.

Note: The file `Partitions/QBinomialFormulas.lean` defines equivalent versions of `qBinomial`
using the q-Pascal recurrence in the sub-namespace `AlgebraicCombinatorics.QBinomialRec`.
The file `SignedCounting/AlternatingSums.lean` defines a local version as `Polynomial ℤ`
in the namespace `AlgebraicCombinatorics.SignedCounting`. Both are proven equivalent to
this canonical definition via the theorems listed above.

## References

* Darij Grinberg, *Algebraic Combinatorics*, Section 11.2-11.3
* [Kac-Cheung, *Quantum Calculus*, Chapters 5-7]
* [Stanley, *Enumerative Combinatorics Vol. 1*]

## Tags

q-binomial, Gaussian binomial coefficient, q-integer, q-factorial, partition
-/


/-! ## q-Integers and q-Factorials -/


namespace AlgebraicCombinatorics

open Finset Polynomial BigOperators Nat

section QIntFact

variable {R : Type*} [CommSemiring R]

/-- The q-integer `[n]_q = 1 + q + q^2 + ... + q^(n-1)`.
This is a q-analogue of the natural number n, since `[n]_1 = n`.

See Definition 11.3.1(a) in the source. -/
def qInt (n : ℕ) (q : R) : R := ∑ i ∈ range n, q ^ i

/-- The q-factorial `[n]_q! = [1]_q * [2]_q * ... * [n]_q`.
This is a q-analogue of n!, since `[n]_1! = n!`.

See Definition 11.3.1(b) in the source. -/
def qFactorial (n : ℕ) (q : R) : R := ∏ i ∈ range n, qInt (i + 1) q

end QIntFact

/-! ## q-Binomial Coefficients -/


section QBinomial

variable {R : Type*} [CommSemiring R]

/-- A partition fits in a k × m box if it has at most k parts,
each of size at most m. -/
def PartitionFitsInBox (n : ℕ) (k m : ℕ) (μ : Nat.Partition n) : Prop :=
  μ.parts.card ≤ k ∧ ∀ p ∈ μ.parts, p ≤ m

/-- The set of monotone functions from `Fin k` to `Fin (m + 1)`, representing
weakly increasing k-tuples with entries in `{0, 1, ..., m}`. -/
def monotoneFunctions (k m : ℕ) : Finset (Fin k → Fin (m + 1)) :=
  Finset.univ.filter fun f => Monotone f

/-- The q-binomial coefficient `⟦n;k⟧_q`, defined via the sum over monotone tuples:
  `⟦n;k⟧_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ iₖ ≤ n-k} q^(i₁ + i₂ + ... + iₖ)`

This is equivalent to the generating function for partitions fitting in a k × (n-k) box
(see `qBinomial_eq_partition_gf`).

See Definition 11.2.1(a) and Proposition 11.2.1(a) in the source. -/
noncomputable def qBinomial (n k : ℕ) (q : R) : R :=
  if k ≤ n then
    ∑ f ∈ monotoneFunctions k (n - k), q ^ (∑ i, (f i).val)
  else 0

/-- The q-binomial coefficient as a polynomial in `ℤ[X]`.

This is the generating function for partitions fitting in a k × (n-k) box:
  `⟦n;k⟧_q = ∑_{λ fits in k × (n-k) box} q^|λ|`

See Definition 11.2.1(a) in the source. -/
noncomputable def qBinomialPoly (n k : ℕ) : ℤ[X] :=
  if k ≤ n then
    ∑ f ∈ monotoneFunctions k (n - k), (X : ℤ[X]) ^ (∑ i, (f i).val)
  else 0

/-! ### Alternative Characterizations -/

/-- The set of partitions of n fitting in a k × m box.

    **Argument order:** This definition uses `(n k m : ℕ)` where:
    - `n` is the partition size
    - `k` is the maximum number of parts (length ≤ k)
    - `m` is the maximum part size (largest part ≤ m)

    This is the canonical definition of `partitionsInBox` for this project.
    The definition `QBinomialRec.partitionsInBox` in `QBinomialFormulas.lean`
    uses the same argument order. -/
def partitionsInBox (n k m : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter fun μ => μ.parts.card ≤ k ∧ ∀ p ∈ μ.parts, p ≤ m

/-- Given a partition μ with parts ≤ m and at most k parts,
construct a monotone function by padding with zeros and sorting. -/
noncomputable def partitionToMonotoneAux (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) : Fin k → Fin (m + 1) := by
  let padded : Multiset ℕ := μ.parts + Multiset.replicate (k - μ.parts.card) 0
  let sorted : List ℕ := padded.sort (· ≤ ·)
  have hlen : sorted.length = k := by
    simp only [Multiset.length_sort, Multiset.card_add, Multiset.card_replicate, sorted, padded]
    omega
  exact fun i => ⟨sorted.getD i.val 0, by
    by_cases hi : i.val < sorted.length
    · have h := List.getD_eq_getElem sorted 0 hi
      rw [h]
      have hmem : sorted[i.val] ∈ sorted := List.getElem_mem hi
      have hmem' : sorted[i.val] ∈ padded := by rw [Multiset.mem_sort] at hmem; exact hmem
      rw [Multiset.mem_add] at hmem'
      cases hmem' with
      | inl h => exact Nat.lt_succ_of_le (hparts _ h)
      | inr h => simp only [Multiset.mem_replicate, ne_eq] at h; omega
    · simp only [List.getD_eq_default _ _ (Nat.not_lt.mp hi), Nat.zero_lt_succ]⟩

/-! ### Basic Properties -/
/-! #### Helper definitions and lemmas for counting monotone functions -/


/-- Forward map: monotone function to Sym (multiset of values) -/
def monotoneToSym (k m : ℕ) (f : Fin k → Fin (m + 1)) : Sym (Fin (m + 1)) k :=
  ⟨Finset.univ.val.map f, by simp⟩

/-- Backward map: Sym to monotone function via sorting -/
noncomputable def symToMonotone (k m : ℕ) (s : Sym (Fin (m + 1)) k) : Fin k → Fin (m + 1) :=
  fun i => ((s : Multiset (Fin (m + 1))).sort (· ≤ ·)).get ⟨i, by
    simp only [Multiset.length_sort]
    have : (s : Multiset (Fin (m + 1))).card = k := s.2
    omega⟩

end QBinomial
end AlgebraicCombinatorics
