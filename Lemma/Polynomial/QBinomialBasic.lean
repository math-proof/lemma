import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Enumerative.QBinomialBasic.Part4
open AlgebraicCombinatorics
open Finset
open Nat
open scoped BigOperators


section
-- ac-theorems


namespace AlgebraicCombinatorics

open Finset Polynomial BigOperators Nat


section QIntFact

variable {R : Type*} [CommSemiring R]

@[simp]
lemma qInt_zero (q : R) : qInt 0 q = 0 := by
  simp [qInt]

@[simp]
lemma qInt_one (q : R) : qInt 1 q = 1 := by
  simp [qInt]

@[simp]
lemma qInt_two (q : R) : qInt 2 q = 1 + q := by
  simp [qInt, sum_range_succ]

lemma qInt_succ (n : ℕ) (q : R) : qInt (n + 1) q = qInt n q + q ^ n := by
  simp [qInt, sum_range_succ]

/-- The q-integer satisfies `[n]_1 = n`.
See Remark 11.3.2 in the source. -/
@[simp]
lemma qInt_one_eq (n : ℕ) : qInt n (1 : R) = n := by
  simp [qInt]

@[simp]
lemma qFactorial_zero (q : R) : qFactorial 0 q = 1 := by
  simp [qFactorial]

@[simp]
lemma qFactorial_one (q : R) : qFactorial 1 q = 1 := by
  simp [qFactorial, qInt_one]

lemma qFactorial_succ (n : ℕ) (q : R) :
    qFactorial (n + 1) q = qFactorial n q * qInt (n + 1) q := by
  simp [qFactorial, prod_range_succ]

/-- The q-factorial satisfies `[n]_1! = n!`.
See Remark 11.3.2 in the source. -/
@[simp]
lemma qFactorial_one_eq (n : ℕ) : qFactorial n (1 : R) = n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ, ih, qInt_one_eq, Nat.factorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- The q-integer as a rational function: `[n]_q = (1 - q^n) / (1 - q)`.
This holds in any ring where `1 - q` is invertible, or as formal power series.

See Remark 11.3.2 in the source. -/
lemma qInt_eq_geom_sum {R : Type*} [CommRing R] (n : ℕ) (q : R) :
    (1 - q) * qInt n q = 1 - q ^ n := by
  induction n with
  | zero => simp [qInt]
  | succ n ih =>
    rw [qInt_succ, mul_add, ih, pow_succ]
    ring

/-- Helper: qFactorial n = (∏ i ∈ range k, qInt (n - i) q) * qFactorial (n - k) when k ≤ n.

This is the key splitting lemma for the factorial form of the q-binomial coefficient.
It states that [n]_q! can be split as:
  [n]_q! = [n]_q · [n-1]_q · ... · [n-k+1]_q · [n-k]_q!
-/
lemma qFactorial_split (n k : ℕ) (hk : k ≤ n) (q : R) :
    qFactorial n q = (∏ i ∈ range k, qInt (n - i) q) * qFactorial (n - k) q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    rw [prod_range_succ, ih hk']
    have h1 : n - k ≥ 1 := by omega
    have h2 : n - k - 1 = n - (k + 1) := by omega
    have h3 : qFactorial (n - k) q = qFactorial (n - k - 1) q * qInt (n - k) q := by
      have hpos : n - k - 1 + 1 = n - k := by omega
      conv_lhs => rw [← hpos, qFactorial_succ]
      simp only [hpos]
    rw [h3, h2]
    ring

/-- qInt n q ≠ 0 when q^n ≠ 1 (i.e., when q is not an n-th root of unity). -/
lemma qInt_ne_zero {R : Type*} [Field R] (n : ℕ) (q : R) (hq : q ^ n ≠ 1) :
    qInt n q ≠ 0 := by
  intro h
  have h1 : (1 - q) * qInt n q = 0 := by rw [h]; ring
  rw [qInt_eq_geom_sum] at h1
  have h2 : q ^ n = 1 := (sub_eq_zero.mp h1).symm
  exact hq h2

/-- qFactorial n q ≠ 0 when q^i ≠ 1 for i = 1, ..., n. -/
lemma qFactorial_ne_zero {R : Type*} [Field R] (n : ℕ) (q : R)
    (hq : ∀ i ∈ range n, q ^ (i + 1) ≠ 1) : qFactorial n q ≠ 0 := by
  simp only [qFactorial, prod_ne_zero_iff]
  intro i hi
  exact qInt_ne_zero (i + 1) q (hq i hi)

end QIntFact


section QBinomial

variable {R : Type*} [CommSemiring R]


/-- The q-binomial is defined as a sum over weakly increasing tuples:
`⟦n;k⟧_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ iₖ ≤ n-k} q^(i₁ + i₂ + ... + iₖ)`

This is the definition, restated for clarity.

See Proposition 11.2.1(a) in the source. -/
lemma qBinomial_eq_sum_increasing_tuples (n k : ℕ) (hk : k ≤ n) (q : R) :
    qBinomial n k q = ∑ f ∈ monotoneFunctions k (n - k), q ^ (∑ i, (f i).val) := by
  simp only [qBinomial, ite_eq_left hk]

/-- Helper lemma: filtering zeros from a multiset preserves the sum. -/
lemma multiset_sum_filter_ne_zero (s : Multiset ℕ) :
    (s.filter (· ≠ 0)).sum = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : a = 0
    · subst ha
      have : (0 ::ₘ s).filter (fun x => x ≠ 0) = s.filter (fun x => x ≠ 0) := by
        exact Multiset.filter_cons_of_neg s (by decide : ¬(0 ≠ 0))
      rw [this]; simp [ih]
    · have : (a ::ₘ s).filter (fun x => x ≠ 0) = a ::ₘ (s.filter (fun x => x ≠ 0)) := by
        exact Multiset.filter_cons_of_pos s ha
      rw [this]; simp [ih]

/-- The constructed monotone function is indeed monotone. -/
lemma partitionToMonotoneAux_monotone (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) :
    Monotone (partitionToMonotoneAux k m s μ hcard hparts) := by
  intro i j hij
  simp only [partitionToMonotoneAux, Fin.mk_le_mk]
  set padded := μ.parts + Multiset.replicate (k - μ.parts.card) 0
  set sorted := padded.sort (· ≤ ·)
  have hlen : sorted.length = k := by
    simp only [Multiset.length_sort, Multiset.card_add, Multiset.card_replicate, sorted, padded]
    omega
  by_cases hi : i.val < sorted.length
  · by_cases hj : j.val < sorted.length
    · rw [List.getD_eq_getElem sorted 0 hi, List.getD_eq_getElem sorted 0 hj]
      have hsorted : sorted.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
      exact List.Pairwise.rel_get_of_le hsorted hij
    · have hj' : j.val ≥ sorted.length := Nat.not_lt.mp hj
      rw [hlen] at hj'
      exact absurd j.isLt (Nat.not_lt.mpr hj')
  · have hi' : i.val ≥ sorted.length := Nat.not_lt.mp hi
    rw [hlen] at hi'
    exact absurd i.isLt (Nat.not_lt.mpr hi')

/-- The sum of the constructed function equals s. -/
lemma partitionToMonotoneAux_sum (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) :
    ∑ i, (partitionToMonotoneAux k m s μ hcard hparts i).val = s := by
  simp only [partitionToMonotoneAux]
  set padded := μ.parts + Multiset.replicate (k - μ.parts.card) 0
  set sorted := padded.sort (· ≤ ·)
  have hlen : sorted.length = k := by
    simp only [Multiset.length_sort, Multiset.card_add, Multiset.card_replicate, sorted, padded]
    omega
  have h1 : ∑ i : Fin k, sorted.getD i.val 0 = sorted.sum := by
    rw [← List.sum_ofFn]; congr 1
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro n hn1 hn2
      simp only [List.getElem_ofFn, List.getD_eq_getElem sorted 0 (by omega : n < sorted.length)]
  rw [h1]
  have h2 : sorted.sum = padded.sum := by
    have heq := Multiset.sort_eq padded (· ≤ ·)
    rw [← Multiset.sum_coe sorted, heq]
  rw [h2, Multiset.sum_add, Multiset.sum_replicate, smul_zero, add_zero]
  exact μ.parts_sum

/-- The multiset of function values equals the padded partition. -/
lemma partitionToMonotoneAux_multiset (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) :
    (↑(List.ofFn fun i => (partitionToMonotoneAux k m s μ hcard hparts i).val) : Multiset ℕ) =
    μ.parts + Multiset.replicate (k - μ.parts.card) 0 := by
  simp only [partitionToMonotoneAux]
  set padded := μ.parts + Multiset.replicate (k - μ.parts.card) 0
  set sorted := padded.sort (· ≤ ·)
  have hlen : sorted.length = k := by
    simp only [Multiset.length_sort, Multiset.card_add, Multiset.card_replicate, sorted, padded]
    omega
  have h_list_eq : List.ofFn (fun i : Fin k => sorted.getD i.val 0) = sorted := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro n hn1 hn2
      simp only [List.getElem_ofFn, List.getD_eq_getElem sorted 0 (by omega : n < sorted.length)]
  rw [h_list_eq]
  exact Multiset.sort_eq padded (· ≤ ·)

/-- Filtering the multiset of function values gives back the partition's parts. -/
lemma partitionToMonotoneAux_roundtrip (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) :
    (↑(List.ofFn fun i => (partitionToMonotoneAux k m s μ hcard hparts i).val) : Multiset ℕ).filter (· ≠ 0) = μ.parts := by
  rw [partitionToMonotoneAux_multiset, Multiset.filter_add]
  have h_filter_parts : μ.parts.filter (· ≠ 0) = μ.parts := by
    rw [Multiset.filter_eq_self]; intro x hx; exact (μ.parts_pos hx).ne'
  have h_filter_zeros : (Multiset.replicate (k - μ.parts.card) 0).filter (· ≠ 0) = 0 := by
    rw [Multiset.filter_eq_nil]; intro x hx
    simp only [Multiset.mem_replicate, ne_eq] at hx; simp [hx.2]
  rw [h_filter_parts, h_filter_zeros, add_zero]

/-- The key bijection lemma: for each s, the number of monotone functions with sum s
equals the number of partitions of s fitting in a k × m box.

This follows from the classical bijection between monotone functions and partitions:
- Forward: f ↦ partition whose parts are the nonzero values of f
- Backward: μ ↦ monotone function obtained by padding μ.parts to k values and sorting

This is equivalent to the stars-and-bars / lattice path correspondence. -/
lemma card_monotoneFunctions_sum_eq (k m s : ℕ) (_hs : s ≤ k * m) :
    ((monotoneFunctions k m).filter fun f => ∑ i, (f i).val = s).card =
    (partitionsInBox s k m).card := by
  apply Finset.card_bij
    (fun f hf => Nat.Partition.ofSums s (↑(List.ofFn fun i => (f i).val) : Multiset ℕ)
      (by simp only [Multiset.sum_coe, List.sum_ofFn]
          simp only [monotoneFunctions, mem_filter] at hf; exact hf.2))
  -- 1. Forward map lands in partitionsInBox
  · intro f hf
    simp only [monotoneFunctions, mem_filter] at hf ⊢
    simp only [partitionsInBox, mem_filter, mem_univ, true_and]
    constructor
    · simp only [Nat.Partition.ofSums_parts]
      calc (Multiset.filter (· ≠ 0) (↑(List.ofFn fun i => (f i).val))).card
          ≤ (↑(List.ofFn fun i => (f i).val) : Multiset ℕ).card :=
            Multiset.card_le_card (Multiset.filter_le _ _)
        _ = k := by simp only [Multiset.coe_card, List.length_ofFn]
    · intro p hp
      have hp' : p ∈ (↑(List.ofFn fun i => (f i).val) : Multiset ℕ).filter (· ≠ 0) := hp
      rw [Multiset.mem_filter, Multiset.mem_coe, List.mem_ofFn] at hp'
      obtain ⟨⟨i, hi⟩, hp2⟩ := hp'
      have : (f i).val < m + 1 := (f i).isLt; omega
  -- 2. Injectivity
  · intro f1 hf1 f2 hf2 heq
    simp only [monotoneFunctions, mem_filter] at hf1 hf2
    have h_filter_eq : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).filter (· ≠ 0) =
        (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).filter (· ≠ 0) := by
      have := congrArg Nat.Partition.parts heq
      simp only [Nat.Partition.ofSums_parts] at this; exact this
    have h_card_eq : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).card =
        (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).card := by
      simp only [Multiset.coe_card, List.length_ofFn]
    have h_multiset_eq : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ) =
        (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ) := by
      ext n
      by_cases hn : n = 0
      · subst hn
        have h1 : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).count 0 =
            k - ((↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).filter (· ≠ 0)).card := by
          have := Multiset.filter_add_not (· ≠ 0) (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ)
          have hc := congrArg Multiset.card this
          simp only [Multiset.card_add, Multiset.coe_card, List.length_ofFn] at hc
          have hf : ((↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).filter (fun x => ¬x ≠ 0)).card =
              (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).count 0 := by
            simp only [ne_eq, not_not, Multiset.count_eq_card_filter_eq, eq_comm]
          omega
        have h2 : (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).count 0 =
            k - ((↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).filter (· ≠ 0)).card := by
          have := Multiset.filter_add_not (· ≠ 0) (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ)
          have hc := congrArg Multiset.card this
          simp only [Multiset.card_add, Multiset.coe_card, List.length_ofFn] at hc
          have hf : ((↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).filter (fun x => ¬x ≠ 0)).card =
              (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).count 0 := by
            simp only [ne_eq, not_not, Multiset.count_eq_card_filter_eq, eq_comm]
          omega
        rw [h1, h2, h_filter_eq]
      · have h1 : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).count n =
            ((↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).filter (· ≠ 0)).count n := by
          symm; exact Multiset.count_filter_of_pos hn
        have h2 : (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).count n =
            ((↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).filter (· ≠ 0)).count n := by
          symm; exact Multiset.count_filter_of_pos hn
        rw [h1, h2, h_filter_eq]
    have h_sort_eq : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).sort (· ≤ ·) =
        (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).sort (· ≤ ·) := by rw [h_multiset_eq]
    have h_sorted1 : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).sort (· ≤ ·) =
        List.ofFn fun i => (f1 i).val := by
      rw [Multiset.coe_sort]; apply List.mergeSort_eq_self
      rw [List.pairwise_ofFn]; intro i j hij; exact hf1.1.2 (Fin.mk_le_mk.mpr (le_of_lt hij))
    have h_sorted2 : (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).sort (· ≤ ·) =
        List.ofFn fun i => (f2 i).val := by
      rw [Multiset.coe_sort]; apply List.mergeSort_eq_self
      rw [List.pairwise_ofFn]; intro i j hij; exact hf2.1.2 (Fin.mk_le_mk.mpr (le_of_lt hij))
    rw [h_sorted1, h_sorted2] at h_sort_eq
    funext i; exact Fin.val_inj.mp (congrFun (List.ofFn_inj.mp h_sort_eq) i)
  -- 3. Surjectivity
  · intro μ hμ
    simp only [partitionsInBox, mem_filter, mem_univ, true_and] at hμ
    refine ⟨partitionToMonotoneAux k m s μ hμ.1 hμ.2, ?_, ?_⟩
    · simp only [monotoneFunctions, mem_filter, mem_univ, true_and]
      exact ⟨partitionToMonotoneAux_monotone k m s μ hμ.1 hμ.2, partitionToMonotoneAux_sum k m s μ hμ.1 hμ.2⟩
    · apply Nat.Partition.ext
      simp only [Nat.Partition.ofSums_parts]
      exact partitionToMonotoneAux_roundtrip k m s μ hμ.1 hμ.2

/-- The q-binomial coefficient equals the generating function for partitions
fitting in a k × (n-k) box.

Note: This requires k ≤ n because when k > n, the LHS is 0 by definition
but the RHS would count the empty partition (giving 1). In the mathematical
definition over ℤ, when k > n, n - k < 0, so no partition has largest part ≤ n - k.
But in Lean with ℕ subtraction, n - k = 0 when k > n, and the empty partition
vacuously satisfies "all parts ≤ 0".

See Definition 11.2.1(a) in the source. -/
lemma qBinomial_eq_partition_gf (n k : ℕ) (hk : k ≤ n) (q : R) :
    qBinomial n k q = ∑ m ∈ range (k * (n - k) + 1),
      (partitionsInBox m k (n - k)).card • q ^ m := by
  simp only [qBinomial, ite_eq_left hk]
  -- Rewrite LHS by grouping by sum
  have hbound : ∀ f ∈ monotoneFunctions k (n - k), ∑ i, (f i).val ∈ range (k * (n - k) + 1) := by
    intro f _
    simp only [mem_range]
    calc ∑ i, (f i).val ≤ ∑ _ : Fin k, (n - k) := by
          apply Finset.sum_le_sum
          intro i _
          exact Nat.lt_succ_iff.mp (f i).isLt
      _ = k * (n - k) := by simp [Finset.sum_const]
      _ < k * (n - k) + 1 := Nat.lt_succ_self _
  -- Use sum_fiberwise
  conv_lhs => rw [← Finset.sum_fiberwise_of_maps_to hbound]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [mem_range] at hs
  -- The fiber sum is ∑ f with sum = s, q^s = (count) • q^s
  have hcard : ((monotoneFunctions k (n - k)).filter fun f => ∑ i, (f i).val = s).card =
      (partitionsInBox s k (n - k)).card := by
    apply card_monotoneFunctions_sum_eq
    omega
  -- Simplify the fiber sum
  have h1 : ∑ f ∈ (monotoneFunctions k (n - k)).filter (fun f => ∑ i, (f i).val = s),
      q ^ (∑ i, (f i).val) =
      ∑ f ∈ (monotoneFunctions k (n - k)).filter (fun f => ∑ i, (f i).val = s), q ^ s := by
    apply Finset.sum_congr rfl
    intro f hf
    simp only [mem_filter] at hf
    rw [hf.2]
  rw [h1, Finset.sum_const, hcard]

/-- The cardinality of monotone functions equals the binomial coefficient -/
lemma card_monotoneFunctions_eq_choose' (k m : ℕ) :
    (monotoneFunctions k m).card = Nat.choose (k + m) k := by
  have h1 : (monotoneFunctions k m).card = Fintype.card { f : Fin k → Fin (m + 1) // Monotone f } := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨f, hf⟩ => ⟨f, by simp [monotoneFunctions] at hf; exact hf⟩
      invFun := fun ⟨f, hf⟩ => ⟨f, by simp [monotoneFunctions]; exact hf⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  rw [h1]
  have h2 : Fintype.card (Sym (Fin (m + 1)) k) = Nat.choose (m + k) k := by
    rw [Sym.card_sym_eq_choose]
    simp [Fintype.card_fin]
  rw [add_comm k m, ← h2]
  exact Fintype.card_congr (monotoneEquivSym k m)

/-- At q = 1, the q-binomial coefficient equals the ordinary binomial coefficient.

See Proposition 11.2.1(c) in the source. -/
@[simp]
lemma qBinomial_one_eq_binomial (n k : ℕ) : qBinomial n k (1 : R) = Nat.choose n k := by
  by_cases hk : k ≤ n
  · unfold qBinomial
    simp only [ite_eq_left hk, one_pow, Finset.sum_const]
    rw [card_monotoneFunctions_eq_choose']
    have h : k + (n - k) = n := Nat.add_sub_cancel' hk
    rw [h]
    simp
  · unfold qBinomial
    simp only [ite_eq_right hk]
    rw [Nat.choose_eq_zero_of_lt (by omega : n < k)]
    simp

/-- The q-binomial coefficient is zero when k > n.

See Proposition 11.2.2 in the source. -/
@[simp]
lemma qBinomial_zero_of_lt (n k : ℕ) (hk : n < k) (q : R) : qBinomial n k q = 0 := by
  simp [qBinomial, Nat.not_le.mpr hk]

/-- `⟦n;0⟧_q = 1` for all n.

See Proposition 11.2.3 in the source. -/
@[simp]
lemma qBinomial_n_zero (n : ℕ) (q : R) : qBinomial n 0 q = 1 := by
  simp only [qBinomial, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  -- Show monotoneFunctions 0 n = Finset.univ
  have h1 : monotoneFunctions 0 n = Finset.univ := by
    ext f
    simp only [monotoneFunctions, mem_filter, mem_univ, true_and, iff_true]
    intro i
    exact Fin.elim0 i
  rw [h1]
  simp

/-- `⟦n;n⟧_q = 1` for all n.

See Proposition 11.2.3 in the source. -/
@[simp]
lemma qBinomial_n_n (n : ℕ) (q : R) : qBinomial n n q = 1 := by
  unfold qBinomial
  simp only [le_refl, ↓reduceIte]
  conv_lhs => rw [Nat.sub_self]
  -- monotoneFunctions n 0 is singleton {fun _ => 0} since Fin 1 has one element
  have h_singleton : (monotoneFunctions n 0) = {fun _ => 0} := by
    ext f
    simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro _
      funext x
      exact @Subsingleton.elim _ Fin.subsingleton_one (f x) 0
    · intro hf
      rw [hf]
      exact fun _ _ _ => le_refl _
  rw [h_singleton, sum_singleton]
  simp only [Fin.val_zero, sum_const_zero, pow_zero]


/-- First recurrence relation for q-binomial coefficients:
`⟦n;k⟧_q = q^(n-k) * ⟦n-1;k-1⟧_q + ⟦n-1;k⟧_q`

This is a q-analogue of Pascal's identity.

Note: The hypothesis `0 < k` is necessary because in Lean with `k : ℕ`, we have `k - 1 = 0`
when `k = 0` due to saturating subtraction. This would make the RHS equal to
`q^n * qBinomial (n-1) 0 q + qBinomial (n-1) 0 q = q^n + 1`, which is not equal to
`qBinomial n 0 q = 1` in general.

See Theorem 11.2.4(a) in the source. The source handles k ∈ ℤ with the convention that
(n choose k)_q = 0 for negative k, and explicitly notes that when k = 0, the identity
reduces to 1 = q^(n-k) * 0 + 1. -/
lemma qBinomial_rec_left (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) (q : R) :
    qBinomial n k q = q ^ (n - k) * qBinomial (n - 1) (k - 1) q + qBinomial (n - 1) k q := by
  by_cases hkn : k ≤ n
  · -- Case k ≤ n
    have hk1 : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hkn 1
    simp only [qBinomial, hkn, hk1, ↓reduceIte]
    have hdim1 : (n - 1) - (k - 1) = n - k := by omega

    by_cases hkn' : k ≤ n - 1
    · -- Subcase k < n (both RHS terms contribute)
      simp only [hkn', ↓reduceIte]
      have hdim2 : (n - 1) - k = n - k - 1 := by omega
      rw [hdim1, hdim2]
      -- The main combinatorial identity requires showing that monotoneFunctions k (n-k)
      -- splits into two parts based on whether f(k-1) = n-k or f(k-1) < n-k.
      -- Type 1 (f(k-1) = n-k) bijects to monotoneFunctions (k-1) (n-k) with sum offset n-k
      -- Type 2 (f(k-1) < n-k) bijects to monotoneFunctions k (n-k-1) with same sum
      -- This is a standard bijection argument in q-binomial theory.
      set m := n - k with hm_def
      have hm_pos : 0 < m := by omega
      -- Define partition sets
      let lastIdx : Fin k := ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩
      let maxVal : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      let S_max := (monotoneFunctions k m).filter fun f => f lastIdx = maxVal
      let S_below := (monotoneFunctions k m).filter fun f => (f lastIdx).val < m
      -- Partition property
      have h_partition : monotoneFunctions k m = S_max ∪ S_below := by
        ext f
        simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_union, S_max, S_below, lastIdx, maxVal]
        constructor
        · intro hf
          have h_bound := (f ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).isLt
          by_cases h : (f ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).val = m
          · left; exact ⟨hf, Fin.ext h⟩
          · right; exact ⟨hf, by omega⟩
        · intro h
          rcases h with ⟨hf, _⟩ | ⟨hf, _⟩ <;> exact hf
      -- Disjointness
      have h_disjoint : Disjoint S_max S_below := by
        simp only [Finset.disjoint_iff_ne, S_max, S_below, mem_filter, lastIdx, maxVal]
        intro f hf g hg heq
        rw [heq] at hf
        simp only [Fin.ext_iff] at hf
        omega
      rw [h_partition, sum_union h_disjoint]
      congr 1
      -- Part 1: S_max sum equals q^m * sum over monotoneFunctions (k-1) m
      · rw [mul_sum]
        refine sum_bij' 
          (fun f _ => fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩)
          (fun g _ => fun i => if h : i.val < k - 1 then g ⟨i.val, h⟩ else maxVal)
          ?_ ?_ ?_ ?_ ?_
        -- hi: forward lands in target
        · intro f hf
          simp only [S_max, mem_filter, monotoneFunctions] at hf
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and]
          intro i j hij
          exact hf.1.2 (Fin.mk_le_mk.mpr hij)
        -- hj: backward lands in source
        · intro g hg
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and] at hg
          simp only [S_max, mem_filter, monotoneFunctions, mem_univ, true_and, lastIdx, maxVal]
          constructor
          · intro i j hij
            beta_reduce
            split_ifs with hi hj hj
            · exact hg (Fin.mk_le_mk.mpr hij)
            · exact Nat.lt_succ_iff.mp (g ⟨i.val, hi⟩).isLt
            · omega
            · exact le_refl _
          · simp only [Nat.lt_irrefl, dite_false]
        -- left_inv
        · intro f hf
          simp only [S_max, mem_filter, lastIdx, maxVal] at hf
          funext i
          by_cases hi : i.val < k - 1
          · simp only [hi, dite_true]
          · simp only [hi, dite_false]
            have h1 := i.isLt
            have h2 : i.val = k - 1 := by omega
            have hi' : i = ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩ := Fin.ext h2
            rw [hi', hf.2]
        -- right_inv
        · intro g hg
          funext i
          simp only [i.isLt, dite_true]
        -- sum relation
        · intro f hf
          simp only [S_max, mem_filter, lastIdx, maxVal] at hf
          have h_sum : ∑ i : Fin k, (f i).val = 
              m + ∑ i : Fin (k - 1), (f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩).val := by
            have h_decomp : (Finset.univ : Finset (Fin k)) = 
                (Finset.univ.filter (fun i => i.val < k - 1)) ∪ 
                (Finset.univ.filter (fun i => i.val = k - 1)) := by
              ext i; simp only [mem_univ, mem_union, mem_filter, true_and, true_iff]; omega
            have h_disj : Disjoint (Finset.univ.filter (fun i : Fin k => i.val < k - 1))
                                   (Finset.univ.filter (fun i : Fin k => i.val = k - 1)) := by
              simp only [disjoint_filter]; intro _ _ h1 h2; omega
            have h_last_eq : (Finset.univ : Finset (Fin k)).filter (fun i => i.val = k - 1) = 
                {⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩} := by
              ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
            calc ∑ i : Fin k, (f i).val 
                = ∑ i ∈ (Finset.univ.filter (fun i => i.val < k - 1)) ∪ 
                       (Finset.univ.filter (fun i => i.val = k - 1)), (f i).val := by rw [← h_decomp]
              _ = ∑ i ∈ Finset.univ.filter (fun i => i.val < k - 1), (f i).val + 
                  ∑ i ∈ Finset.univ.filter (fun i => i.val = k - 1), (f i).val := sum_union h_disj
              _ = ∑ i ∈ Finset.univ.filter (fun i => i.val < k - 1), (f i).val + 
                  (f ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).val := by rw [h_last_eq, sum_singleton]
              _ = ∑ i ∈ Finset.univ.filter (fun i => i.val < k - 1), (f i).val + m := by
                    simp only [hf.2, Fin.val_mk]
              _ = m + ∑ i ∈ Finset.univ.filter (fun i => i.val < k - 1), (f i).val := by ring
              _ = m + ∑ i : Fin (k - 1), (f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩).val := by
                    congr 1
                    have h_filter_eq : (Finset.univ : Finset (Fin k)).filter (fun i => i.val < k - 1) = 
                        Finset.univ.image (fun i : Fin (k - 1) => 
                          ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩) := by
                      ext i
                      simp only [mem_filter, mem_univ, true_and, mem_image]
                      constructor
                      · intro hi; exact ⟨⟨i.val, hi⟩, by ext; rfl⟩
                      · intro ⟨j, hj⟩; simp only [Fin.ext_iff] at hj; rw [← hj]; exact j.isLt
                    rw [h_filter_eq, sum_image]
                    intro i _ j _ hij
                    simp only [Fin.mk.injEq] at hij
                    exact Fin.ext hij
          rw [h_sum, pow_add, mul_comm]
      -- Part 2: S_below sum equals sum over monotoneFunctions k (m-1)
      · have hm' : m - 1 + 1 = m := by omega
        refine sum_bij'
          (fun f hf => fun i => ⟨(f i).val, by
            simp only [S_below, mem_filter, monotoneFunctions, lastIdx] at hf
            have h_mono := hf.1.2
            have h_last := hf.2
            have h_bound : (f i).val ≤ (f ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).val := 
              h_mono (by simp only [Fin.le_def]; omega)
            omega⟩)
          (fun g _ => fun i => ⟨(g i).val, by have h := (g i).isLt; omega⟩)
          ?_ ?_ ?_ ?_ ?_
        -- hi: forward lands in target
        · intro f hf
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and]
          simp only [S_below, mem_filter, monotoneFunctions] at hf
          intro i j hij
          simp only [Fin.mk_le_mk]
          exact hf.1.2 hij
        -- hj: backward lands in source
        · intro g hg
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and] at hg
          simp only [S_below, mem_filter, monotoneFunctions, mem_univ, true_and, lastIdx]
          constructor
          · intro i j hij
            simp only [Fin.mk_le_mk]
            exact hg hij
          · have h := (g ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).isLt
            omega
        -- left_inv
        · intro f hf; funext i; rfl
        -- right_inv
        · intro g hg; funext i; rfl
        -- sum relation
        · intro f hf; rfl
    · -- Subcase k = n
      have hkn_eq : k = n := by omega
      have hn1k : n - 1 < k := Nat.not_le.mp hkn'
      simp only [Nat.not_le.mpr hn1k, ↓reduceIte, add_zero]
      rw [hkn_eq, Nat.sub_self, pow_zero, one_mul, Nat.sub_self]
      -- monotoneFunctions m 0 = {fun _ => 0} for any m
      have hmono_n : monotoneFunctions n 0 = {fun _ => 0} := by
        ext f
        simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro _; funext x; exact @Subsingleton.elim _ Fin.subsingleton_one (f x) 0
        · intro hf; rw [hf]; exact fun _ _ _ => le_refl _
      have hmono_n1 : monotoneFunctions (n - 1) 0 = {fun _ => 0} := by
        ext f
        simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro _; funext x; exact @Subsingleton.elim _ Fin.subsingleton_one (f x) 0
        · intro hf; rw [hf]; exact fun _ _ _ => le_refl _
      rw [hmono_n, hmono_n1, sum_singleton, sum_singleton]
      simp [sum_const_zero]
  · -- Case k > n: LHS = 0
    have hkn1 : ¬(k - 1 ≤ n - 1) := by omega
    have hkn2 : ¬(k ≤ n - 1) := by omega
    simp only [qBinomial, hkn, hkn1, hkn2, ↓reduceIte, mul_zero, add_zero]

lemma transposeMonotone_monotone (k m : ℕ) (f : Fin k → Fin (m + 1)) (_hf : Monotone f) :
    Monotone (transposeMonotone k m f) := by
  intro j1 j2 hj
  simp only [transposeMonotone, Fin.mk_le_mk]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

lemma profile_le_iff (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : Monotone f)
    (i : Fin k) (j : Fin m) :
    (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card ≤ i.val ↔
    j.val ≥ m - (f i).val := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hfi : (f i).val ≤ m - 1 - j.val := by omega
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val) := by
      intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic] at hi' ⊢
      exact Nat.le_trans (hf hi') hfi
    have : i.val + 1 ≤ (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card := by
      calc i.val + 1 = (Finset.Iic i).card := by simp [Fin.card_Iic]
        _ ≤ _ := Finset.card_le_card hsub
    omega
  · intro h
    have hfi : (f i).val > m - 1 - j.val := by omega
    have hsub : Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val) ⊆ Finset.Iio i := by
      intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio] at hi' ⊢
      by_contra hne
      push Not at hne
      have : (f i).val ≤ (f i').val := hf hne
      omega
    calc (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card
        ≤ (Finset.Iio i).card := Finset.card_le_card hsub
      _ = i.val := by simp [Fin.card_Iio]

lemma count_ge_complement (m v : ℕ) (hv : v ≤ m) :
    (Finset.univ.filter (fun j : Fin m => j.val ≥ m - v)).card = v := by
  cases m with
  | zero => simp; omega
  | succ m' =>
    have hv' : v ≤ m' + 1 := hv
    have h_inj : Function.Injective (fun x : Fin v => (⟨x.val + (m' + 1 - v), by omega⟩ : Fin (m' + 1))) := by
      intro a b hab; simp only [Fin.mk.injEq] at hab; ext; omega
    have h_eq : (Finset.univ.filter (fun j : Fin (m' + 1) => j.val ≥ m' + 1 - v)) =
                Finset.map ⟨fun x : Fin v => ⟨x.val + (m' + 1 - v), by omega⟩, h_inj⟩ Finset.univ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro hj; use ⟨j.val - (m' + 1 - v), by omega⟩; ext; simp; omega
      · intro ⟨a, ha⟩; simp only [Fin.ext_iff] at ha; omega
    rw [h_eq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma transposeMonotone_involutive (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : Monotone f) :
    transposeMonotone m k (transposeMonotone k m f) = f := by
  funext i
  simp only [transposeMonotone]
  have key : ∀ j : Fin m,
      ((Finset.univ.filter (fun i' : Fin k => (f i').val > m - 1 - j.val)).card > k - 1 - i.val) ↔
      (j.val ≥ m - (f i).val) := by
    intro j
    have h_compl : (Finset.univ.filter (fun i' : Fin k => (f i').val > m - 1 - j.val)).card =
                   k - (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card := by
      have h_eq : (Finset.univ.filter (fun i' : Fin k => (f i').val > m - 1 - j.val)) =
                  Finset.univ \ (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)) := by
        ext i'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]; omega
      rw [h_eq, Finset.card_sdiff]
      have h_inter : (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)) ∩ Finset.univ =
                     (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)) := Finset.inter_univ _
      rw [h_inter]; simp only [Finset.card_univ, Fintype.card_fin]
    rw [h_compl]
    have hcard : (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card ≤ k := by
      calc _ ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = k := Finset.card_fin k
    constructor
    · intro h
      have h2 : (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card ≤ i.val := by
        omega
      exact (profile_le_iff k m f hf i j).mp h2
    · intro h
      have h2 := (profile_le_iff k m f hf i j).mpr h
      omega
  simp_rw [key]
  have hfi : (f i).val ≤ m := Nat.lt_succ_iff.mp (f i).isLt
  rw [Fin.ext_iff]
  exact count_ge_complement m (f i).val hfi

lemma sum_transposeMonotone (k m : ℕ) (f : Fin k → Fin (m + 1)) :
    ∑ j : Fin m, (transposeMonotone k m f j).val = ∑ i : Fin k, (f i).val := by
  simp only [transposeMonotone]
  simp_rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  trans (Finset.univ.filter (fun j : Fin m => (f i).val > m - 1 - j.val)).card
  · rw [Finset.card_eq_sum_ones]; simp only [Finset.sum_filter]
  · have hfi : (f i).val ≤ m := Nat.lt_succ_iff.mp (f i).isLt
    have key : ∀ j : Fin m, ((f i).val > m - 1 - j.val) ↔ (j.val ≥ m - (f i).val) := by
      intro j; have hj : j.val < m := j.isLt; omega
    simp_rw [key]
    exact count_ge_complement m (f i).val hfi

lemma transposeMonotone_mem (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : f ∈ monotoneFunctions k m) :
    transposeMonotone k m f ∈ monotoneFunctions m k := by
  simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
  exact transposeMonotone_monotone k m f hf

/-- Local symmetry lemma for use in qBinomial_rec_right proof. -/
lemma qBinomial_symm_local (n k : ℕ) (hk : k ≤ n) (q : R) :
    qBinomial n k q = qBinomial n (n - k) q := by
  have hnk : n - k ≤ n := Nat.sub_le n k
  have h_eq : n - (n - k) = k := Nat.sub_sub_self hk
  simp only [qBinomial, hk, hnk, ite_true]
  conv_rhs => rw [h_eq]
  apply Finset.sum_bij'
    (fun f _ => transposeMonotone k (n - k) f)
    (fun g _ => transposeMonotone (n - k) k g)
  · intro f hf; exact transposeMonotone_mem k (n - k) f hf
  · intro g hg; exact transposeMonotone_mem (n - k) k g hg
  · intro f hf
    simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact transposeMonotone_involutive k (n - k) f hf
  · intro g hg
    simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact transposeMonotone_involutive (n - k) k g hg
  · intro f _
    congr 1
    exact (sum_transposeMonotone k (n - k) f).symm


/-- Second recurrence relation for q-binomial coefficients:
`⟦n;k⟧_q = ⟦n-1;k-1⟧_q + q^k * ⟦n-1;k⟧_q`

This is another q-analogue of Pascal's identity.

Note: The hypothesis `0 < k` is necessary because in Lean with `k : ℕ`, we have `k - 1 = 0`
when `k = 0` due to saturating subtraction. This would make the RHS equal to
`qBinomial (n-1) 0 q + q^0 * qBinomial (n-1) 0 q = 1 + 1 = 2`, which is not equal to
`qBinomial n 0 q = 1`.

See Theorem 11.2.4(b) in the source. The source handles k ∈ ℤ with the convention that
(n choose k)_q = 0 for negative k. -/
lemma qBinomial_rec_right (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) (q : R) :
    qBinomial n k q = qBinomial (n - 1) (k - 1) q + q ^ k * qBinomial (n - 1) k q := by
  -- Use symmetry: qBinomial n k = qBinomial n (n-k)
  -- Then use rec_left on qBinomial n (n-k)
  -- qBinomial n (n-k) = q^k * qBinomial (n-1) (n-k-1) + qBinomial (n-1) (n-k)
  -- Then use symmetry again to convert back
  by_cases hkn : k ≤ n
  · -- Case k ≤ n
    have hnk : n - k ≤ n := Nat.sub_le n k
    by_cases h_nk_pos : 0 < n - k
    · -- Case n - k > 0
      rw [qBinomial_symm_local n k hkn]
      rw [qBinomial_rec_left n hn (n - k) h_nk_pos]
      -- Now we have: q ^ (n - (n-k)) * qBinomial (n-1) (n-k-1) + qBinomial (n-1) (n-k)
      have h1 : n - (n - k) = k := Nat.sub_sub_self hkn
      rw [h1]
      -- Need to show the terms match
      have h3 : n - 1 - (n - k) = k - 1 := by omega
      have hk' : k ≤ n - 1 ∨ k = n := by omega
      cases hk' with
      | inl hk' =>
        -- k ≤ n - 1
        have h4 : qBinomial (n - 1) (n - k - 1) q = qBinomial (n - 1) (n - 1 - (n - k - 1)) q := by
          apply qBinomial_symm_local
          omega
        have h5 : n - 1 - (n - k - 1) = k := by omega
        rw [h4, h5]
        have h6 : qBinomial (n - 1) (n - k) q = qBinomial (n - 1) (n - 1 - (n - k)) q := by
          apply qBinomial_symm_local
          omega
        rw [h6, h3]
        ring
      | inr hk' =>
        -- k = n contradicts h_nk_pos since n - k = 0 when k = n
        have : n - k = 0 := by omega
        omega
    · -- Case n - k = 0, i.e., k = n
      push Not at h_nk_pos
      have hkn' : k = n := by omega
      rw [hkn']
      simp only [qBinomial_n_n]
      have h1 : qBinomial (n - 1) n q = 0 := qBinomial_zero_of_lt (n - 1) n (by omega) q
      rw [h1]
      simp
  · -- Case k > n
    push Not at hkn
    simp only [qBinomial_zero_of_lt n k hkn]
    have h1 : qBinomial (n - 1) (k - 1) q = 0 := qBinomial_zero_of_lt (n - 1) (k - 1) (by omega) q
    have h2 : qBinomial (n - 1) k q = 0 := qBinomial_zero_of_lt (n - 1) k (by omega) q
    rw [h1, h2]
    simp


-- Helper lemma: relates products with shifted indices
lemma prod_n_shift {R : Type*} [CommRing R] (k n : ℕ) (q : R) (hk : k ≤ n) :
    (1 - q ^ n) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) =
    (∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k)) := by
  induction k with
  | zero =>
    simp only [prod_range_zero, mul_one, one_mul, Nat.sub_zero]
  | succ k ih =>
    rw [prod_range_succ, prod_range_succ]
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have ih' := ih hk'
    calc (1 - q ^ n) * ((∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) * (1 - q ^ (n - (k + 1))))
        = ((1 - q ^ n) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) * (1 - q ^ (n - (k + 1))) := by ring
      _ = ((∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k))) * (1 - q ^ (n - (k + 1))) := by rw [ih']
      _ = (∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k)) * (1 - q ^ (n - (k + 1))) := by ring

-- Helper lemma: simplifies product index shift
lemma prod_shift {R : Type*} [CommRing R] (k n : ℕ) (q : R) (hn : k ≤ n) :
    ∏ i ∈ range k, (1 - q ^ (n - 1 - i)) = ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) := by
  apply prod_congr rfl
  intro i hi
  have hi' : i < k := mem_range.mp hi
  have : n - 1 - i = n - (i + 1) := by omega
  rw [this]

/-- Product formula for q-binomial coefficients (polynomial identity):
`(1-q^k)(1-q^(k-1))...(1-q) * ⟦n;k⟧_q = (1-q^n)(1-q^(n-1))...(1-q^(n-k+1))`

This is Theorem thm.pars.qbinom.quot1 part (a) from the source.
Also known as Theorem 11.2.5(a) in the section numbering.

The identity holds over any commutative ring without requiring any divisibility conditions.
This is the "polynomial form" that avoids fractions, making it easier to substitute values
for q without worrying about whether denominators are invertible. -/
lemma qBinomial_quot_formula {R : Type*} [CommRing R] (n k : ℕ) (hk : k ≤ n) (q : R) :
    (∏ i ∈ range k, (1 - q ^ (i + 1))) * qBinomial n k q =
    ∏ i ∈ range k, (1 - q ^ (n - i)) := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hn : 0 < n := Nat.lt_of_lt_of_le (Nat.succ_pos k) hk
      have hk' : k ≤ n - 1 := by omega
      rw [qBinomial_rec_left n hn (k + 1) (Nat.succ_pos k)]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [prod_range_succ, mul_add]
      have ih1 := ih (n - 1) (Nat.sub_lt hn (Nat.succ_pos 0)) k hk'
      rw [prod_range_succ]
      have eq1 : (∏ i ∈ range k, (1 - q ^ (i + 1))) * (1 - q ^ (k + 1)) *
          (q ^ (n - (k + 1)) * qBinomial (n - 1) k q) =
          (1 - q ^ (k + 1)) * q ^ (n - (k + 1)) * (∏ i ∈ range k, (1 - q ^ (n - 1 - i))) := by
        rw [← ih1]
        ring
      rw [eq1]
      rw [prod_shift k n q (le_of_lt (Nat.lt_of_succ_le hk))]
      by_cases hcase : k + 1 = n
      · -- Case k + 1 = n, so qBinomial (n-1) (k+1) = 0
        have h0 : qBinomial (n - 1) (k + 1) q = 0 := by
          rw [hcase]
          apply qBinomial_zero_of_lt
          omega
        rw [h0, mul_zero, add_zero]
        have hnk1 : n - (k + 1) = 0 := by omega
        have hnk : n - k = 1 := by omega
        rw [hnk1, hnk, pow_zero, mul_one, pow_one, hcase]
        have hshift := prod_n_shift k n q (le_of_lt (Nat.lt_of_succ_le hk))
        have hnk' : n - k = 1 := by omega
        rw [hnk'] at hshift
        simp only [pow_one] at hshift
        exact hshift
      · -- Case k + 1 < n
        have hkn : k + 1 < n := Nat.lt_of_le_of_ne hk hcase
        have hk''' : k + 1 ≤ n - 1 := by omega
        have ih2 := ih (n - 1) (Nat.sub_lt hn (Nat.succ_pos 0)) (k + 1) hk'''
        rw [prod_range_succ, prod_range_succ] at ih2
        have hnk1 : (n - 1) - k = n - (k + 1) := by omega
        rw [hnk1] at ih2
        rw [prod_shift k n q (le_of_lt (Nat.lt_of_succ_le hk))] at ih2
        rw [ih2]
        have key : (1 - q ^ (k + 1)) * q ^ (n - (k + 1)) + (1 - q ^ (n - (k + 1))) = 1 - q ^ n := by
          calc (1 - q ^ (k + 1)) * q ^ (n - (k + 1)) + (1 - q ^ (n - (k + 1)))
              = q ^ (n - (k + 1)) - q ^ (k + 1) * q ^ (n - (k + 1)) + 1 - q ^ (n - (k + 1)) := by ring
            _ = 1 - q ^ (k + 1) * q ^ (n - (k + 1)) := by ring
            _ = 1 - q ^ (k + 1 + (n - (k + 1))) := by rw [← pow_add]
            _ = 1 - q ^ n := by rw [Nat.add_sub_cancel' (Nat.le_of_lt hkn)]
        calc (1 - q ^ (k + 1)) * q ^ (n - (k + 1)) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) +
                (∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) * (1 - q ^ (n - (k + 1)))
            = (∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) *
                ((1 - q ^ (k + 1)) * q ^ (n - (k + 1)) + (1 - q ^ (n - (k + 1)))) := by ring
          _ = (∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) * (1 - q ^ n) := by rw [key]
          _ = (1 - q ^ n) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) := by ring
          _ = (∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k)) :=
              prod_n_shift k n q (le_of_lt (Nat.lt_of_succ_le hk))

/-- Product formula for q-binomial coefficients (quotient form):
`⟦n;k⟧_q = ∏_{i=0}^{k-1} (1-q^(n-i)) / (1-q^(i+1))`

This is Theorem thm.pars.qbinom.quot1 part (b) from the source.
Also known as Theorem 11.2.5(b) in the section numbering.

This holds in any ring where the denominator is invertible. The hypothesis `hq` ensures
that `q` is not a root of unity of order ≤ k, which guarantees all factors `(1 - q^(i+1))`
in the denominator are nonzero.

Note: Part (b) is the more intuitive statement showing the q-binomial as a ratio of
products, but part (a) (`qBinomial_quot_formula`) is easier to work with when substituting
values for q since it has no denominators. -/
lemma qBinomial_eq_prod_quot {R : Type*} [Field R] (n k : ℕ) (hk : k ≤ n)
    (q : R) (hq : ∀ i ∈ range k, q ^ (i + 1) ≠ 1) :
    qBinomial n k q = ∏ i ∈ range k, (1 - q ^ (n - i)) / (1 - q ^ (i + 1)) := by
  have h := qBinomial_quot_formula n k hk q
  -- The product ∏ i ∈ range k, (1 - q ^ (i + 1)) is nonzero
  have hne : ∏ i ∈ range k, (1 - q ^ (i + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    simp only [sub_ne_zero, ne_eq]
    exact (hq i hi).symm
  -- Divide both sides by the product
  rw [Finset.prod_div_distrib]
  rw [← h]
  field_simp [hne]

/-- q-binomial coefficient in terms of q-integers (falling factorial form):
`⟦n;k⟧_q = [n]_q * [n-1]_q * ... * [n-k+1]_q / [k]_q!`

See Theorem 11.2.6 in the source. -/
lemma qBinomial_eq_qInt_prod_quot {R : Type*} [Field R] (n k : ℕ) (hk : k ≤ n)
    (q : R) (hq : ∀ i ∈ range k, q ^ (i + 1) ≠ 1) :
    qBinomial n k q = (∏ i ∈ range k, qInt (n - i) q) / qFactorial k q := by
  -- First, use qBinomial_eq_prod_quot
  rw [qBinomial_eq_prod_quot n k hk q hq]
  -- Get the hypothesis that q ≠ 1 (from hq at i = 0 when k > 0)
  by_cases hk0 : k = 0
  · -- When k = 0, both sides are empty products
    simp [hk0, qFactorial]
  · -- When k > 0, we have q ≠ 1 from hq
    have hq1 : q ≠ 1 := by
      have h0 : 0 ∈ range k := by simp [Nat.pos_of_ne_zero hk0]
      specialize hq 0 h0
      simp at hq
      exact hq
    have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr hq1)
    -- Helper: qInt m q = (1 - q ^ m) / (1 - q) when q ≠ 1
    have hqInt : ∀ m, qInt m q = (1 - q ^ m) / (1 - q) := fun m => by
      rw [eq_div_iff h1q, mul_comm, qInt_eq_geom_sum]
    -- Rewrite the numerator product
    have eq1 : (∏ i ∈ range k, qInt (n - i) q) = ∏ i ∈ range k, (1 - q ^ (n - i)) / (1 - q) := by
      apply prod_congr rfl
      intro i _
      exact hqInt (n - i)
    -- Rewrite qFactorial
    have eq2 : qFactorial k q = ∏ i ∈ range k, (1 - q ^ (i + 1)) / (1 - q) := by
      simp only [qFactorial]
      apply prod_congr rfl
      intro i _
      exact hqInt (i + 1)
    rw [eq1, eq2]
    -- Now both sides are products of divisions
    rw [prod_div_distrib, prod_div_distrib]
    -- Simplify the constant products
    simp only [prod_const, card_range]
    -- Simplify RHS: (A / B) / (C / B) = A / C
    rw [div_div]
    -- Now need to show: A / C = A / (B * (C / B))
    congr 1
    -- Goal: ∏ x ∈ range k, (1 - q ^ (x + 1)) = (1 - q) ^ k * (∏ i ∈ range k, (1 - q ^ (i + 1)) / (1 - q))
    conv_rhs =>
      rw [show (1 - q) ^ k = ∏ _ ∈ range k, (1 - q) by simp [prod_const, card_range]]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    field_simp

/-- q-binomial coefficient in terms of q-factorials:
`⟦n;k⟧_q = [n]_q! / ([k]_q! * [n-k]_q!)`

See Theorem 11.2.6 in the source.
This is also Theorem thm.pars.qbinom.quot2 from the text. -/
lemma qBinomial_eq_qFactorial_quot {R : Type*} [Field R] (n k : ℕ) (hk : k ≤ n)
    (q : R) (hq : ∀ i ∈ range n, q ^ (i + 1) ≠ 1) :
    qBinomial n k q = qFactorial n q / (qFactorial k q * qFactorial (n - k) q) := by
  -- First, derive the hypothesis needed for qBinomial_eq_qInt_prod_quot
  have hq' : ∀ i ∈ range k, q ^ (i + 1) ≠ 1 := by
    intro i hi
    apply hq i
    exact mem_range.mpr (Nat.lt_of_lt_of_le (mem_range.mp hi) hk)
  -- Use the falling factorial form
  rw [qBinomial_eq_qInt_prod_quot n k hk q hq']
  -- Use the split formula: qFactorial n q = (∏ i ∈ range k, qInt (n - i) q) * qFactorial (n - k) q
  rw [qFactorial_split n k hk q]
  -- Show the denominators are nonzero
  have hne_k : qFactorial k q ≠ 0 := qFactorial_ne_zero k q hq'
  have hq_nk : ∀ i ∈ range (n - k), q ^ (i + 1) ≠ 1 := by
    intro i hi
    apply hq i
    exact mem_range.mpr (Nat.lt_of_lt_of_le (mem_range.mp hi) (Nat.sub_le n k))
  have hne_nk : qFactorial (n - k) q ≠ 0 := qFactorial_ne_zero (n - k) q hq_nk
  field_simp [hne_k, hne_nk]


/-- Symmetry of q-binomial coefficients: `⟦n;k⟧_q = ⟦n;n-k⟧_q`.

See Proposition 11.2.7 in the source. -/
lemma qBinomial_symm (n k : ℕ) (hk : k ≤ n) (q : R) :
    qBinomial n k q = qBinomial n (n - k) q := by
  have hnk : n - k ≤ n := Nat.sub_le n k
  have h_eq : n - (n - k) = k := Nat.sub_sub_self hk
  simp only [qBinomial, hk, hnk, ite_true]
  conv_rhs => rw [h_eq]
  apply Finset.sum_bij'
    (fun f _ => transposeMonotone k (n - k) f)
    (fun g _ => transposeMonotone (n - k) k g)
  · intro f hf; exact transposeMonotone_mem k (n - k) f hf
  · intro g hg; exact transposeMonotone_mem (n - k) k g hg
  · intro f hf
    simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact transposeMonotone_involutive k (n - k) f hf
  · intro g hg
    simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact transposeMonotone_involutive (n - k) k g hg
  · intro f _
    congr 1
    exact (sum_transposeMonotone k (n - k) f).symm

end QBinomial


section PartitionCount

/-- The number of partitions with at most k parts and largest part at most ℓ
equals the number of monotone functions from `Fin k` to `Fin (ℓ + 1)`,
which is the binomial coefficient `(k + ℓ) choose k`.

This is a consequence of the bijection between such partitions and lattice paths
from (0,0) to (ℓ,k) using east and north steps.

See discussion before Proposition 11.1.1 in the source. -/
lemma card_monotoneFunctions_eq_choose (k ℓ : ℕ) :
    (monotoneFunctions k ℓ).card = Nat.choose (k + ℓ) k := by
  -- monotoneFunctions k ℓ is a Finset of functions Fin k → Fin (ℓ + 1) that are monotone
  -- Its cardinality equals the cardinality of {f : Fin k → Fin (ℓ + 1) // Monotone f}
  have h1 : (monotoneFunctions k ℓ).card = Fintype.card {f : Fin k → Fin (ℓ + 1) // Monotone f} := by
    simp only [monotoneFunctions, card_filter, Fintype.card_subtype]
  rw [h1]
  -- Use the equivalence with Sym
  rw [Fintype.card_congr (monotoneFunctionsEquivSym k ℓ)]
  -- Use the stars and bars theorem
  rw [Sym.card_sym_eq_multichoose, Nat.multichoose_eq]
  simp only [Fintype.card_fin]
  -- Now simplify: (ℓ + 1 + k - 1).choose k = (k + ℓ).choose k
  congr 1
  omega

/-- The number of partitions with exactly k parts and largest part exactly ℓ
equals the binomial coefficient `(k + ℓ - 2) choose (k - 1)`.

This counts lattice paths from (0,0) to (ℓ,k) that start with an east step
and end with a north step.

See Proposition 11.1.1 in the source. -/
lemma card_partitions_with_parts_and_largest (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) :
    (monotoneFunctions (k - 1) (ℓ - 1)).card = Nat.choose (k + ℓ - 2) (k - 1) := by
  rw [card_monotoneFunctions_eq_choose]
  congr 1
  omega

end PartitionCount


section Examples

end Examples

end AlgebraicCombinatorics
end


/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_int_eq_geom_sum_eq
-- given
  {R : Type*} [CommRing R] (n : ℕ) (q : R) :
-- imply
  (1 - q) * AlgebraicCombinatorics.qInt n q = 1 - q ^ n := by
-- proof
  apply AlgebraicCombinatorics.qInt_eq_geom_sum n q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_factorial_one_eq
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) :
-- imply
  AlgebraicCombinatorics.qFactorial n (1 : R) = n ! := by
-- proof
  apply AlgebraicCombinatorics.qFactorial_one_eq n

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_sum_increasing_tuples_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    ∑ f ∈ AlgebraicCombinatorics.monotoneFunctions k (n - k),
      q ^ (∑ i, (f i).val) := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_sum_increasing_tuples n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_partition_gf_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    ∑ m ∈ range (k * (n - k) + 1),
      (AlgebraicCombinatorics.partitionsInBox m k (n - k)).card • q ^ m := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_partition_gf n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_one_eq_binomial_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) :
-- imply
  AlgebraicCombinatorics.qBinomial n k (1 : R) = Nat.choose n k := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_one_eq_binomial n k

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_zero_of_lt_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hk : n < k) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q = 0 := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_zero_of_lt n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_n_zero_eq
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n 0 q = 1 := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_n_zero n q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_n_n_eq
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n n q = 1 := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_n_n n q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_rec_left_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    q ^ (n - k) * AlgebraicCombinatorics.qBinomial (n - 1) (k - 1) q +
      AlgebraicCombinatorics.qBinomial (n - 1) k q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_rec_left n hn k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_rec_right_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    AlgebraicCombinatorics.qBinomial (n - 1) (k - 1) q +
      q ^ k * AlgebraicCombinatorics.qBinomial (n - 1) k q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_rec_right n hn k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_quot_formula_eq
-- given
  {R : Type*} [CommRing R] (n k : ℕ) (hk : k ≤ n) (q : R) :
-- imply
  (∏ i ∈ range k, (1 - q ^ (i + 1))) * AlgebraicCombinatorics.qBinomial n k q =
    ∏ i ∈ range k, (1 - q ^ (n - i)) := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_quot_formula n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_prod_quot_eq
-- given
  {R : Type*} [Field R] (n k : ℕ) (q : R) (hk : k ≤ n)
  (hq : ∀ i ∈ range k, q ^ (i + 1) ≠ 1) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    ∏ i ∈ range k, (1 - q ^ (n - i)) / (1 - q ^ (i + 1)) := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_prod_quot n k hk q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_q_int_prod_quot_eq
-- given
  {R : Type*} [Field R] (n k : ℕ) (q : R) (hk : k ≤ n)
  (hq : ∀ i ∈ range k, q ^ (i + 1) ≠ 1) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    (∏ i ∈ range k, AlgebraicCombinatorics.qInt (n - i) q) /
      AlgebraicCombinatorics.qFactorial k q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_qInt_prod_quot n k hk q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_q_factorial_quot_eq
-- given
  {R : Type*} [Field R] (n k : ℕ) (q : R) (hk : k ≤ n)
  (hq : ∀ i ∈ range n, q ^ (i + 1) ≠ 1) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    AlgebraicCombinatorics.qFactorial n q /
      (AlgebraicCombinatorics.qFactorial k q *
        AlgebraicCombinatorics.qFactorial (n - k) q) := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_qFactorial_quot n k hk q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_symm_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q = AlgebraicCombinatorics.qBinomial n (n - k) q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_symm n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma card_monotone_functions_sum_eq
-- given
  (k m s : ℕ) (hs : s ≤ k * m) :
-- imply
  ((AlgebraicCombinatorics.monotoneFunctions k m).filter fun f =>
      ∑ i, (f i).val = s).card =
    (AlgebraicCombinatorics.partitionsInBox s k m).card := by
-- proof
  apply AlgebraicCombinatorics.card_monotoneFunctions_sum_eq k m s hs

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma card_monotone_functions_eq_choose_eq
-- given
  (k ℓ : ℕ) :
-- imply
  (AlgebraicCombinatorics.monotoneFunctions k ℓ).card = Nat.choose (k + ℓ) k := by
-- proof
  apply AlgebraicCombinatorics.card_monotoneFunctions_eq_choose k ℓ

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma card_partitions_with_parts_and_largest_eq
-- given
  (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) :
-- imply
  (AlgebraicCombinatorics.monotoneFunctions (k - 1) (ℓ - 1)).card =
    Nat.choose (k + ℓ - 2) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.card_partitions_with_parts_and_largest k ℓ hk hℓ

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_int_ne_zero_is
-- given
  {R : Type*} [Field R] (n : ℕ) (q : R) (hq : q ^ n ≠ 1) :
-- imply
  AlgebraicCombinatorics.qInt n q ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.qInt_ne_zero n q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_factorial_ne_zero_is
-- given
  {R : Type*} [Field R] (n : ℕ) (q : R)
  (hq : ∀ i ∈ range n, q ^ (i + 1) ≠ 1) :
-- imply
  AlgebraicCombinatorics.qFactorial n q ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.qFactorial_ne_zero n q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma transpose_monotone_involutive_eq
-- given
  (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : Monotone f) :
-- imply
  AlgebraicCombinatorics.transposeMonotone m k
    (AlgebraicCombinatorics.transposeMonotone k m f) = f := by
-- proof
  apply AlgebraicCombinatorics.transposeMonotone_involutive k m f hf

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma sum_transpose_monotone_eq
-- given
  (k m : ℕ) (f : Fin k → Fin (m + 1)) :
-- imply
  ∑ j : Fin m, (AlgebraicCombinatorics.transposeMonotone k m f j).val =
    ∑ i : Fin k, (f i).val := by
-- proof
  apply AlgebraicCombinatorics.sum_transposeMonotone k m f

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qInt_zero
  [CommSemiring R]
-- given
  (q : R) :
-- imply
  AlgebraicCombinatorics.qInt 0 q = 0 := by
-- proof
  apply AlgebraicCombinatorics.qInt_zero q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qInt_one
  [CommSemiring R]
-- given
  (q : R) :
-- imply
  AlgebraicCombinatorics.qInt 1 q = 1 := by
-- proof
  apply AlgebraicCombinatorics.qInt_one q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qInt_two
  [CommSemiring R]
-- given
  (q : R) :
-- imply
  AlgebraicCombinatorics.qInt 2 q = 1 + q := by
-- proof
  apply AlgebraicCombinatorics.qInt_two q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qInt_succ
  [CommSemiring R]
-- given
  (n : ℕ)
  (q : R) :
-- imply
  AlgebraicCombinatorics.qInt (n + 1) q = AlgebraicCombinatorics.qInt n q + q ^ n := by
-- proof
  apply AlgebraicCombinatorics.qInt_succ n q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qInt_one_eq
  [CommSemiring R]
-- given
  (n : ℕ) :
-- imply
  AlgebraicCombinatorics.qInt n (1 : R) = n := by
-- proof
  apply AlgebraicCombinatorics.qInt_one_eq n

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qFactorial_zero
  [CommSemiring R]
-- given
  (q : R) :
-- imply
  AlgebraicCombinatorics.qFactorial 0 q = 1 := by
-- proof
  apply AlgebraicCombinatorics.qFactorial_zero q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qFactorial_succ
  [CommSemiring R]
-- given
  (n : ℕ)
  (q : R) :
-- imply
  AlgebraicCombinatorics.qFactorial (n + 1) q = AlgebraicCombinatorics.qFactorial n q * AlgebraicCombinatorics.qInt (n + 1) q := by
-- proof
  apply AlgebraicCombinatorics.qFactorial_succ n q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qFactorial_split
  [CommSemiring R]
-- given
  (n k : ℕ)
  (hk : k ≤ n)
  (q : R) :
-- imply
  AlgebraicCombinatorics.qFactorial n q = (∏ i ∈ Finset.range k, AlgebraicCombinatorics.qInt (n - i) q) * AlgebraicCombinatorics.qFactorial (n - k) q := by
-- proof
  apply AlgebraicCombinatorics.qFactorial_split n k hk q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma x_qFactorial_one
  [CommSemiring R]
-- given
  (q : R) :
-- imply
  AlgebraicCombinatorics.qFactorial 1 q = 1 := by
-- proof
  apply AlgebraicCombinatorics.qFactorial_one q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_multiset_sum_filter_ne_zero
-- given
  (s : Multiset ℕ) :
-- imply
  (s.filter (· ≠ 0)).sum = s.sum := by
-- proof
  apply AlgebraicCombinatorics.multiset_sum_filter_ne_zero s

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_partitionToMonotoneAux_monotone
-- given
  (k m s : ℕ)
  (μ : Nat.Partition s)
  (hcard : μ.parts.card ≤ k)
  (hparts : ∀ p ∈ μ.parts, p ≤ m) :
-- imply
  Monotone (partitionToMonotoneAux k m s μ hcard hparts) := by
-- proof
  apply AlgebraicCombinatorics.partitionToMonotoneAux_monotone k m s μ hcard hparts

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_partitionToMonotoneAux_sum
-- given
  (k m s : ℕ)
  (μ : Nat.Partition s)
  (hcard : μ.parts.card ≤ k)
  (hparts : ∀ p ∈ μ.parts, p ≤ m) :
-- imply
  ∑ i, (partitionToMonotoneAux k m s μ hcard hparts i).val = s := by
-- proof
  apply AlgebraicCombinatorics.partitionToMonotoneAux_sum k m s μ hcard hparts

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_partitionToMonotoneAux_multiset
-- given
  (k m s : ℕ)
  (μ : Nat.Partition s)
  (hcard : μ.parts.card ≤ k)
  (hparts : ∀ p ∈ μ.parts, p ≤ m) :
-- imply
  (↑(List.ofFn fun i => (partitionToMonotoneAux k m s μ hcard hparts i).val) : Multiset ℕ) = μ.parts + Multiset.replicate (k - μ.parts.card) 0 := by
-- proof
  apply AlgebraicCombinatorics.partitionToMonotoneAux_multiset k m s μ hcard hparts

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_partitionToMonotoneAux_roundtrip
-- given
  (k m s : ℕ)
  (μ : Nat.Partition s)
  (hcard : μ.parts.card ≤ k)
  (hparts : ∀ p ∈ μ.parts, p ≤ m) :
-- imply
  (↑(List.ofFn fun i => (partitionToMonotoneAux k m s μ hcard hparts i).val) : Multiset ℕ).filter (· ≠ 0) = μ.parts := by
-- proof
  apply AlgebraicCombinatorics.partitionToMonotoneAux_roundtrip k m s μ hcard hparts

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_symToMonotone_monotone
-- given
  (k m : ℕ)
  (s : Sym (Fin (m + 1)) k) :
-- imply
  Monotone (symToMonotone k m s) := by
-- proof
  apply AlgebraicCombinatorics.symToMonotone_monotone k m s

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_monotone_sort_eq
-- given
  (k m : ℕ)
  (f : Fin k → Fin (m + 1))
  (hf : Monotone f) :
-- imply
  symToMonotone k m (monotoneToSym k m f) = f := by
-- proof
  apply AlgebraicCombinatorics.monotone_sort_eq k m f hf

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sym_monotone_sort_eq
-- given
  (k m : ℕ)
  (s : Sym (Fin (m + 1)) k) :
-- imply
  monotoneToSym k m (symToMonotone k m s) = s := by
-- proof
  apply AlgebraicCombinatorics.sym_monotone_sort_eq k m s

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_card_monotoneFunctions_eq_choose'
-- given
  (k m : ℕ) :
-- imply
  (monotoneFunctions k m).card = Nat.choose (k + m) k := by
-- proof
  apply AlgebraicCombinatorics.card_monotoneFunctions_eq_choose' k m

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_transposeMonotone_monotone
-- given
  (k m : ℕ)
  (f : Fin k → Fin (m + 1))
  (hf : Monotone f) :
-- imply
  Monotone (transposeMonotone k m f) := by
-- proof
  apply AlgebraicCombinatorics.transposeMonotone_monotone k m f hf

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_profile_le_iff
-- given
  (k m : ℕ)
  (f : Fin k → Fin (m + 1))
  (hf : Monotone f)
  (i : Fin k)
  (j : Fin m) :
-- imply
  (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card ≤ i.val ↔ j.val ≥ m - (f i).val := by
-- proof
  apply AlgebraicCombinatorics.profile_le_iff k m f hf i j

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_count_ge_complement
-- given
  (m v : ℕ)
  (hv : v ≤ m) :
-- imply
  (Finset.univ.filter (fun j : Fin m => j.val ≥ m - v)).card = v := by
-- proof
  apply AlgebraicCombinatorics.count_ge_complement m v hv

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_transposeMonotone_mem
-- given
  (k m : ℕ)
  (f : Fin k → Fin (m + 1))
  (hf : f ∈ monotoneFunctions k m) :
-- imply
  transposeMonotone k m f ∈ monotoneFunctions m k := by
-- proof
  apply AlgebraicCombinatorics.transposeMonotone_mem k m f hf

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_qBinomial_symm_local
  [CommSemiring R]
-- given
  (n k : ℕ)
  (hk : k ≤ n)
  (q : R) :
-- imply
  qBinomial n k q = qBinomial n (n - k) q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_symm_local n k hk q

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_prod_n_shift
  [CommRing R]
-- given
  (k n : ℕ)
  (hk : k ≤ n)
  (q : R) :
-- imply
  (1 - q ^ n) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) = (∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k)) := by
-- proof
  apply AlgebraicCombinatorics.prod_n_shift k n q hk

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_prod_shift
  [CommRing R]
-- given
  (k n : ℕ)
  (hn : k ≤ n)
  (q : R) :
-- imply
  ∏ i ∈ range k, (1 - q ^ (n - 1 - i)) = ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) := by
-- proof
  apply AlgebraicCombinatorics.prod_shift k n q hn

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_monotoneFunctions_2_1_eq :
-- imply
  monotoneFunctions 2 1 = {f00, f01, f11} := by
-- proof
  apply AlgebraicCombinatorics.monotoneFunctions_2_1_eq

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_f00 :
-- imply
  ∑ i : Fin 2, (f00 i).val = 0 := by
-- proof
  apply AlgebraicCombinatorics.sum_f00

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_f01 :
-- imply
  ∑ i : Fin 2, (f01 i).val = 1 := by
-- proof
  apply AlgebraicCombinatorics.sum_f01

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_f11 :
-- imply
  ∑ i : Fin 2, (f11 i).val = 2 := by
-- proof
  apply AlgebraicCombinatorics.sum_f11

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_monotoneFunctions_2_2_eq :
-- imply
  monotoneFunctions 2 2 = {g00, g01, g02, g11, g12, g22} := by
-- proof
  apply AlgebraicCombinatorics.monotoneFunctions_2_2_eq

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_g00 :
-- imply
  ∑ i : Fin 2, (g00 i).val = 0 := by
-- proof
  apply AlgebraicCombinatorics.sum_g00

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_g01 :
-- imply
  ∑ i : Fin 2, (g01 i).val = 1 := by
-- proof
  apply AlgebraicCombinatorics.sum_g01

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_g02 :
-- imply
  ∑ i : Fin 2, (g02 i).val = 2 := by
-- proof
  apply AlgebraicCombinatorics.sum_g02

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_g11 :
-- imply
  ∑ i : Fin 2, (g11 i).val = 2 := by
-- proof
  apply AlgebraicCombinatorics.sum_g11

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_g12 :
-- imply
  ∑ i : Fin 2, (g12 i).val = 3 := by
-- proof
  apply AlgebraicCombinatorics.sum_g12

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_g22 :
-- imply
  ∑ i : Fin 2, (g22 i).val = 4 := by
-- proof
  apply AlgebraicCombinatorics.sum_g22

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_monotoneFunctions_2_3_eq :
-- imply
  monotoneFunctions 2 3 = {h00, h01, h02, h03, h11, h12, h13, h22, h23, h33} := by
-- proof
  apply AlgebraicCombinatorics.monotoneFunctions_2_3_eq

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h00 :
-- imply
  ∑ i : Fin 2, (h00 i).val = 0 := by
-- proof
  apply AlgebraicCombinatorics.sum_h00

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h01 :
-- imply
  ∑ i : Fin 2, (h01 i).val = 1 := by
-- proof
  apply AlgebraicCombinatorics.sum_h01

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h02 :
-- imply
  ∑ i : Fin 2, (h02 i).val = 2 := by
-- proof
  apply AlgebraicCombinatorics.sum_h02

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h03 :
-- imply
  ∑ i : Fin 2, (h03 i).val = 3 := by
-- proof
  apply AlgebraicCombinatorics.sum_h03

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h11 :
-- imply
  ∑ i : Fin 2, (h11 i).val = 2 := by
-- proof
  apply AlgebraicCombinatorics.sum_h11

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h12 :
-- imply
  ∑ i : Fin 2, (h12 i).val = 3 := by
-- proof
  apply AlgebraicCombinatorics.sum_h12

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h13 :
-- imply
  ∑ i : Fin 2, (h13 i).val = 4 := by
-- proof
  apply AlgebraicCombinatorics.sum_h13

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h22 :
-- imply
  ∑ i : Fin 2, (h22 i).val = 4 := by
-- proof
  apply AlgebraicCombinatorics.sum_h22

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h23 :
-- imply
  ∑ i : Fin 2, (h23 i).val = 5 := by
-- proof
  apply AlgebraicCombinatorics.sum_h23

/--
[QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean)
-/
@[path]
private lemma pv_sum_h33 :
-- imply
  ∑ i : Fin 2, (h33 i).val = 6 := by
-- proof
  apply AlgebraicCombinatorics.sum_h33


-- created on 2026-10-11
-- updated on 2026-10-26
