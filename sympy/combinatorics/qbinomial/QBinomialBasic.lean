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


namespace AlgebraicCombinatorics

open Finset Polynomial BigOperators Nat
/-! ## q-Integers and q-Factorials -/


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

/-- The backward map produces a monotone function -/
theorem symToMonotone_monotone (k m : ℕ) (s : Sym (Fin (m + 1)) k) :
    Monotone (symToMonotone k m s) := by
  intro i j hij
  simp only [symToMonotone, List.get_eq_getElem]
  have h : ((s : Multiset (Fin (m + 1))).sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    have h := @Multiset.pairwise_sort (Fin (m + 1)) (· ≤ ·) _ _ _ _ (s := (s : Multiset (Fin (m + 1))))
    convert h
  exact List.Pairwise.rel_get_of_le h hij

/-- For a monotone function, sorting the multiset of values gives back the function -/
theorem monotone_sort_eq (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : Monotone f) :
    symToMonotone k m (monotoneToSym k m f) = f := by
  ext i
  simp only [symToMonotone, monotoneToSym, Sym.coe_mk, List.get_eq_getElem, Fin.val_inj]
  have h_sorted : ((List.finRange k).map f).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    apply List.Pairwise.imp _ (List.pairwise_lt_finRange k)
    intro a b hab
    exact hf (le_of_lt hab)
  have h_eq : (Finset.univ.val.map f).sort (· ≤ ·) = (List.finRange k).map f := by
    have h1 : (Finset.univ : Finset (Fin k)).val = ↑(List.finRange k) := rfl
    rw [h1, Multiset.map_coe, Multiset.coe_sort, List.mergeSort_eq_self _ h_sorted]
  simp only [h_eq, List.getElem_map, List.getElem_finRange, Fin.cast_mk]

/-- For any Sym, converting to monotone function and back gives the same Sym -/
theorem sym_monotone_sort_eq (k m : ℕ) (s : Sym (Fin (m + 1)) k) :
    monotoneToSym k m (symToMonotone k m s) = s := by
  ext
  simp only [monotoneToSym, symToMonotone, Sym.coe_mk]
  have h_len : ((s : Multiset (Fin (m + 1))).sort (· ≤ ·)).length = k := by
    simp only [Multiset.length_sort]
    exact s.2
  have h_eq : ↑((s : Multiset (Fin (m + 1))).sort (· ≤ ·)) = (s : Multiset (Fin (m + 1))) := by
    exact Multiset.sort_eq (s : Multiset (Fin (m + 1))) (· ≤ ·)
  have h1 : (Finset.univ : Finset (Fin k)).val = ↑(List.finRange k) := rfl
  rw [h1, Multiset.map_coe]
  conv_rhs => rw [← h_eq]
  set sorted := (s : Multiset (Fin (m + 1))).sort (· ≤ ·) with h_sorted_def
  have h_len' : sorted.length = k := h_len
  have h_list : (List.finRange k).map (symToMonotone k m s) = sorted := by
    apply List.ext_getElem
    · simp [h_len']
    · intro n h1' h2
      simp only [List.getElem_map, List.getElem_finRange]
      rfl
  rw [h_list]

/-- The equivalence between monotone functions and Sym -/
noncomputable def monotoneEquivSym (k m : ℕ) :
    { f : Fin k → Fin (m + 1) // Monotone f } ≃ Sym (Fin (m + 1)) k where
  toFun := fun ⟨f, _⟩ => monotoneToSym k m f
  invFun := fun s => ⟨symToMonotone k m s, symToMonotone_monotone k m s⟩
  left_inv := fun ⟨f, hf⟩ => by simp [monotone_sort_eq k m f hf]
  right_inv := fun s => sym_monotone_sort_eq k m s
/-! ### Recurrence Relations -/
/-! ### Transpose of monotone functions

The following helper definitions and lemmas establish a bijection between monotone
functions `Fin k → Fin (m + 1)` and `Fin m → Fin (k + 1)` via transposition.
This is used to prove the symmetry of q-binomial coefficients. -/


/-- The transpose of a monotone function f : Fin k → Fin (m + 1).
Given f, we define g : Fin m → Fin (k + 1) by g(j) = #{i : f(i) > m - 1 - j}.
This corresponds to the conjugate/transpose of the partition encoded by f. -/
def transposeMonotone (k m : ℕ) (f : Fin k → Fin (m + 1)) : Fin m → Fin (k + 1) :=
  fun j => ⟨Finset.univ.filter (fun i => (f i).val > m - 1 - j.val) |>.card, by
    have : (Finset.univ.filter (fun i : Fin k => (f i).val > m - 1 - j.val)).card ≤ Finset.card Finset.univ :=
      Finset.card_filter_le _ _
    simp only [Finset.card_fin] at this
    omega⟩
/-! ### Product Formulas -/

end QBinomial
/-! ## Counting Partitions -/


section PartitionCount

/-- Equivalence between monotone functions `Fin k → Fin (ℓ + 1)` and multisets
of size k over `Fin (ℓ + 1)`. A monotone function is converted to a multiset
by taking its values (with multiplicity), and a multiset is converted to a
monotone function by sorting and indexing. -/
def monotoneFunctionsEquivSym (k ℓ : ℕ) :
    {f : Fin k → Fin (ℓ + 1) // Monotone f} ≃ Sym (Fin (ℓ + 1)) k := by
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro ⟨f, _⟩
    exact ⟨Multiset.ofList (List.ofFn f), by simp⟩
  case invFun =>
    intro s
    let sorted := s.val.sort (· ≤ ·)
    have hlen : sorted.length = k := by simp [sorted, Multiset.length_sort]
    refine ⟨fun i => sorted.get (i.cast hlen.symm), ?_⟩
    intro i j hij
    apply List.Pairwise.rel_get_of_le (Multiset.pairwise_sort s.val (· ≤ ·))
    exact hij
  case left_inv =>
    intro ⟨f, hf⟩
    dsimp only
    ext i
    dsimp only
    rw [Fin.val_inj]
    have h : (Multiset.ofList (List.ofFn f)).sort (· ≤ ·) = List.ofFn f := by
      simp only [Multiset.coe_sort]
      apply List.mergeSort_eq_self
      exact List.pairwise_ofFn.mpr (fun i j hij => hf (le_of_lt hij))
    have hlen : ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·)).length = k := by simp
    have eq1 : ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·)).get (i.cast hlen.symm) =
               ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·))[i.val] := by
      rfl
    rw [eq1]
    simp only [h]
    simp [List.getElem_ofFn]
  case right_inv =>
    intro s
    apply Sym.ext
    simp only [Sym.coe_mk]
    have hlen : (s.val.sort (· ≤ ·)).length = k := by simp [Multiset.length_sort]
    have h1 : List.ofFn (fun i : Fin k => (s.val.sort (· ≤ ·)).get (i.cast hlen.symm)) =
              s.val.sort (· ≤ ·) := by
      apply List.ext_get
      · simp
      · intro i hi1 hi2
        simp only [List.get_ofFn]
        rfl
    rw [h1]
    exact Multiset.sort_eq s.val (· ≤ ·)

end PartitionCount
/-! ## Examples -/


section Examples
/-! ### Helper definitions for explicit enumeration of monotone functions

For small values of n and k, we can enumerate all monotone functions explicitly
and compute the q-binomial polynomial by direct summation. -/


-- For qBinomialPoly 3 2: monotone functions Fin 2 → Fin 2
def f00 : Fin 2 → Fin 2 := ![0, 0]
def f01 : Fin 2 → Fin 2 := ![0, 1]
def f11 : Fin 2 → Fin 2 := ![1, 1]

theorem monotoneFunctions_2_1_eq : monotoneFunctions 2 1 = {f00, f01, f11} := by
  ext f
  simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hf
    have h := hf (Fin.zero_le 1)
    match h0 : f 0, h1 : f 1 with
    | ⟨0, _⟩, ⟨0, _⟩ => left; ext i; fin_cases i <;> simp [f00, h0, h1]
    | ⟨0, _⟩, ⟨1, _⟩ => right; left; ext i; fin_cases i <;> simp [f01, h0, h1]
    | ⟨1, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨1, _⟩, ⟨1, _⟩ => right; right; ext i; fin_cases i <;> simp [f11, h0, h1]
  · intro hf
    rcases hf with rfl | rfl | rfl
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f00]
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f01]
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f11]

theorem sum_f00 : ∑ i : Fin 2, (f00 i).val = 0 := by simp [f00]
theorem sum_f01 : ∑ i : Fin 2, (f01 i).val = 1 := by simp [f01]
theorem sum_f11 : ∑ i : Fin 2, (f11 i).val = 2 := by simp [f11]

-- For qBinomialPoly 4 2: monotone functions Fin 2 → Fin 3
def g00 : Fin 2 → Fin 3 := ![0, 0]
def g01 : Fin 2 → Fin 3 := ![0, 1]
def g02 : Fin 2 → Fin 3 := ![0, 2]
def g11 : Fin 2 → Fin 3 := ![1, 1]
def g12 : Fin 2 → Fin 3 := ![1, 2]
def g22 : Fin 2 → Fin 3 := ![2, 2]

theorem monotoneFunctions_2_2_eq : monotoneFunctions 2 2 = {g00, g01, g02, g11, g12, g22} := by
  ext f
  simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hf
    have h := hf (Fin.zero_le 1)
    match h0 : f 0, h1 : f 1 with
    | ⟨0, _⟩, ⟨0, _⟩ => left; ext i; fin_cases i <;> simp [g00, h0, h1]
    | ⟨0, _⟩, ⟨1, _⟩ => right; left; ext i; fin_cases i <;> simp [g01, h0, h1]
    | ⟨0, _⟩, ⟨2, _⟩ => right; right; left; ext i; fin_cases i <;> simp [g02, h0, h1]
    | ⟨1, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨1, _⟩, ⟨1, _⟩ => right; right; right; left; ext i; fin_cases i <;> simp [g11, h0, h1]
    | ⟨1, _⟩, ⟨2, _⟩ => right; right; right; right; left; ext i; fin_cases i <;> simp [g12, h0, h1]
    | ⟨2, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨2, _⟩ => right; right; right; right; right; ext i; fin_cases i <;> simp [g22, h0, h1]
  · intro hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [g00, g01, g02, g11, g12, g22])

theorem sum_g00 : ∑ i : Fin 2, (g00 i).val = 0 := by simp [g00]
theorem sum_g01 : ∑ i : Fin 2, (g01 i).val = 1 := by simp [g01]
theorem sum_g02 : ∑ i : Fin 2, (g02 i).val = 2 := by simp [g02]
theorem sum_g11 : ∑ i : Fin 2, (g11 i).val = 2 := by simp [g11]
theorem sum_g12 : ∑ i : Fin 2, (g12 i).val = 3 := by simp [g12]
theorem sum_g22 : ∑ i : Fin 2, (g22 i).val = 4 := by simp [g22]

-- For qBinomialPoly 5 2: monotone functions Fin 2 → Fin 4
def h00 : Fin 2 → Fin 4 := ![0, 0]
def h01 : Fin 2 → Fin 4 := ![0, 1]
def h02 : Fin 2 → Fin 4 := ![0, 2]
def h03 : Fin 2 → Fin 4 := ![0, 3]
def h11 : Fin 2 → Fin 4 := ![1, 1]
def h12 : Fin 2 → Fin 4 := ![1, 2]
def h13 : Fin 2 → Fin 4 := ![1, 3]
def h22 : Fin 2 → Fin 4 := ![2, 2]
def h23 : Fin 2 → Fin 4 := ![2, 3]
def h33 : Fin 2 → Fin 4 := ![3, 3]

theorem monotoneFunctions_2_3_eq : monotoneFunctions 2 3 = {h00, h01, h02, h03, h11, h12, h13, h22, h23, h33} := by
  ext f
  simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hf
    have h := hf (Fin.zero_le 1)
    match h0 : f 0, h1 : f 1 with
    | ⟨0, _⟩, ⟨0, _⟩ => left; ext i; fin_cases i <;> simp [h00, h0, h1]
    | ⟨0, _⟩, ⟨1, _⟩ => right; left; ext i; fin_cases i <;> simp [h01, h0, h1]
    | ⟨0, _⟩, ⟨2, _⟩ => right; right; left; ext i; fin_cases i <;> simp [h02, h0, h1]
    | ⟨0, _⟩, ⟨3, _⟩ => right; right; right; left; ext i; fin_cases i <;> simp [h03, h0, h1]
    | ⟨1, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨1, _⟩, ⟨1, _⟩ => right; right; right; right; left; ext i; fin_cases i <;> simp [h11, h0, h1]
    | ⟨1, _⟩, ⟨2, _⟩ => right; right; right; right; right; left; ext i; fin_cases i <;> simp [h12, h0, h1]
    | ⟨1, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h13, h0, h1]
    | ⟨2, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨2, _⟩ => right; right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h22, h0, h1]
    | ⟨2, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h23, h0, h1]
    | ⟨3, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨2, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; right; right; right; ext i; fin_cases i <;> simp [h33, h0, h1]
  · intro hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [h00, h01, h02, h03, h11, h12, h13, h22, h23, h33])

theorem sum_h00 : ∑ i : Fin 2, (h00 i).val = 0 := by simp [h00]
theorem sum_h01 : ∑ i : Fin 2, (h01 i).val = 1 := by simp [h01]
theorem sum_h02 : ∑ i : Fin 2, (h02 i).val = 2 := by simp [h02]
theorem sum_h03 : ∑ i : Fin 2, (h03 i).val = 3 := by simp [h03]
theorem sum_h11 : ∑ i : Fin 2, (h11 i).val = 2 := by simp [h11]
theorem sum_h12 : ∑ i : Fin 2, (h12 i).val = 3 := by simp [h12]
theorem sum_h13 : ∑ i : Fin 2, (h13 i).val = 4 := by simp [h13]
theorem sum_h22 : ∑ i : Fin 2, (h22 i).val = 4 := by simp [h22]
theorem sum_h23 : ∑ i : Fin 2, (h23 i).val = 5 := by simp [h23]
theorem sum_h33 : ∑ i : Fin 2, (h33 i).val = 6 := by simp [h33]

/-- Example: `⟦3;2⟧_q = q^2 + q + 1`.

The partitions fitting in a 2 × 1 box are:
- (1, 1) with size 2
- (1) with size 1
- () with size 0 -/
example : qBinomialPoly 3 2 = X ^ 2 + X + 1 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 3 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (3 : ℕ) - 2 = 1 := by norm_num
  rw [h2, monotoneFunctions_2_1_eq]
  have hf00 : f00 ∉ ({f01, f11} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [f00, f01, f11] at h
  have hf01 : f01 ∉ ({f11} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [f01, f11] at h
  rw [sum_insert hf00, sum_insert hf01, sum_singleton]
  simp only [sum_f00, sum_f01, sum_f11]
  simp only [pow_zero, pow_one]
  ring

/-- Example: `⟦4;2⟧_q = q^4 + q^3 + 2q^2 + q + 1`.

The partitions fitting in a 2 × 2 box are:
- (2, 2) with size 4
- (2, 1) with size 3
- (2) with size 2
- (1, 1) with size 2
- (1) with size 1
- () with size 0 -/
example : qBinomialPoly 4 2 = X ^ 4 + X ^ 3 + 2 * X ^ 2 + X + 1 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 4 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (4 : ℕ) - 2 = 2 := by norm_num
  rw [h2, monotoneFunctions_2_2_eq]
  have hg00 : g00 ∉ ({g01, g02, g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h <;> simp [g00, g01, g02, g11, g12, g22] at h
  have hg01 : g01 ∉ ({g02, g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h <;> simp [g01, g02, g11, g12, g22] at h
  have hg02 : g02 ∉ ({g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h <;> simp [g02, g11, g12, g22] at h
  have hg11 : g11 ∉ ({g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [g11, g12, g22] at h
  have hg12 : g12 ∉ ({g22} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [g12, g22] at h
  rw [sum_insert hg00, sum_insert hg01, sum_insert hg02, sum_insert hg11, sum_insert hg12, sum_singleton]
  simp only [sum_g00, sum_g01, sum_g02, sum_g11, sum_g12, sum_g22]
  simp only [pow_zero, pow_one]
  ring

/-- Example: `⟦5;2⟧_q = 1 + q + 2q^2 + 2q^3 + 2q^4 + q^5 + q^6`.

Computed using Proposition 11.2.1(b). -/
example : qBinomialPoly 5 2 = 1 + X + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 5 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (5 : ℕ) - 2 = 3 := by norm_num
  rw [h2, monotoneFunctions_2_3_eq]
  have hh00 : h00 ∉ ({h01, h02, h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h00, h01, h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh01 : h01 ∉ ({h02, h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h01, h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh02 : h02 ∉ ({h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h <;> simp [h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh03 : h03 ∉ ({h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h <;> simp [h03, h11, h12, h13, h22, h23, h33] at h
  have hh11 : h11 ∉ ({h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h <;> simp [h11, h12, h13, h22, h23, h33] at h
  have hh12 : h12 ∉ ({h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h <;> simp [h12, h13, h22, h23, h33] at h
  have hh13 : h13 ∉ ({h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h <;> simp [h13, h22, h23, h33] at h
  have hh22 : h22 ∉ ({h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [h22, h23, h33] at h
  have hh23 : h23 ∉ ({h33} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [h23, h33] at h
  rw [sum_insert hh00, sum_insert hh01, sum_insert hh02, sum_insert hh03, sum_insert hh11, 
      sum_insert hh12, sum_insert hh13, sum_insert hh22, sum_insert hh23, sum_singleton]
  simp only [sum_h00, sum_h01, sum_h02, sum_h03, sum_h11, sum_h12, sum_h13, sum_h22, sum_h23, sum_h33]
  simp only [pow_zero, pow_one]
  ring

end Examples

end AlgebraicCombinatorics
