import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Young.MonomialSymmetric.Part6
import Lemma.Partition.NPartition
open MvPolynomial hiding R
open Finset
open Equiv
open AlgebraicCombinatorics.SymmetricFunctions hiding NPartition
open AlgebraicCombinatorics.SymmetricFunctions.NPartition
open scoped Polynomial BigOperators


section
-- ac-theorems


open scoped Polynomial
open MvPolynomial Finset Equiv

namespace AlgebraicCombinatorics

namespace SymmetricFunctions

variable {R : Type*} [CommSemiring R]
variable {N : ℕ}


variable {σ : Type*}

namespace NPartition
lemma ofPartition_injective (n : ℕ) :
    Function.Injective (fun x : {p : Nat.Partition n // Multiset.card p.parts ≤ N} =>
      ofPartition x.val x.property) := by
  intro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ heq
  simp only [Subtype.mk.injEq]
  have hparts : (ofPartition p₁ hp₁).parts = (ofPartition p₂ hp₂).parts := by
    simp only at heq
    rw [heq]
  have hsorted : p₁.parts.sort (· ≥ ·) = p₂.parts.sort (· ≥ ·) := by
    have len1 : (p₁.parts.sort (· ≥ ·)).length = Multiset.card p₁.parts := Multiset.length_sort ..
    have len2 : (p₂.parts.sort (· ≥ ·)).length = Multiset.card p₂.parts := Multiset.length_sort ..
    apply List.ext_get
    · by_contra hne
      rcases Nat.lt_trichotomy (p₁.parts.sort (· ≥ ·)).length (p₂.parts.sort (· ≥ ·)).length with hlt | heq' | hgt
      · have hi : (p₁.parts.sort (· ≥ ·)).length < N := Nat.lt_of_lt_of_le hlt (len2.symm ▸ hp₂)
        let idx : Fin N := ⟨(p₁.parts.sort (· ≥ ·)).length, hi⟩
        have h1 : (ofPartition p₁ hp₁).parts idx = 0 := by
          simp only [_root_.NPartition.ofPartition, idx]
          split_ifs with h
          · omega
          · rfl
        have h2 : (ofPartition p₂ hp₂).parts idx ≠ 0 := by
          simp only [_root_.NPartition.ofPartition, idx]
          split_ifs with h
          · have hmem : (p₂.parts.sort (· ≥ ·))[(p₁.parts.sort (· ≥ ·)).length]'h ∈ p₂.parts := by
              exact (Multiset.mem_sort _).mp (List.getElem_mem h)
            exact Nat.pos_iff_ne_zero.mp (p₂.parts_pos hmem)
          · omega
        rw [hparts] at h1
        exact h2 h1
      · exact hne heq'
      · have hi : (p₂.parts.sort (· ≥ ·)).length < N := Nat.lt_of_lt_of_le hgt (len1.symm ▸ hp₁)
        let idx : Fin N := ⟨(p₂.parts.sort (· ≥ ·)).length, hi⟩
        have h1 : (ofPartition p₂ hp₂).parts idx = 0 := by
          simp only [_root_.NPartition.ofPartition, idx]
          split_ifs with h
          · omega
          · rfl
        have h2 : (ofPartition p₁ hp₁).parts idx ≠ 0 := by
          simp only [_root_.NPartition.ofPartition, idx]
          split_ifs with h
          · have hmem : (p₁.parts.sort (· ≥ ·))[(p₂.parts.sort (· ≥ ·)).length]'h ∈ p₁.parts := by
              exact (Multiset.mem_sort _).mp (List.getElem_mem h)
            exact Nat.pos_iff_ne_zero.mp (p₁.parts_pos hmem)
          · omega
        rw [hparts] at h2
        exact h2 h1
    · intro i hi1 hi2
      have hi1' : i < N := Nat.lt_of_lt_of_le hi1 (len1.symm ▸ hp₁)
      have hfun := congr_fun hparts ⟨i, hi1'⟩
      simp only [_root_.NPartition.ofPartition] at hfun
      simp only [dif_pos hi1, dif_pos hi2] at hfun
      exact hfun
  apply Nat.Partition.ext_iff.mpr
  rw [← Multiset.sort_eq p₁.parts (· ≥ ·), ← Multiset.sort_eq p₂.parts (· ≥ ·), hsorted]

/-- The bijection between partitions of length ≤ N and N-partitions
    (Proposition prop.sf.Npar-as-par)

    This is a corollary of `equivPartition` stating that the map is bijective. -/
lemma bijection_partition (n : ℕ) :
    Function.Bijective (fun x : {p : Nat.Partition n // Multiset.card p.parts ≤ N} =>
      (equivPartition n x : {mu : NPartition N // mu.size = n})) :=
  (equivPartition n).bijective

end NPartition

/-- Coefficient of the monomial x^a in monomialExp a is 1. -/
@[simp]
lemma monomialExp_coeff_self (a : Fin N → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm a) (monomialExp a : MvPolynomial (Fin N) R) = 1 := by
  simp [monomialExp_eq_monomial, coeff, coeff_monomial]

/-- Coefficient of a different monomial in monomialExp a is 0. -/
lemma monomialExp_coeff_ne (a b : Fin N → ℕ) (h : a ≠ b) :
    coeff (Finsupp.equivFunOnFinite.symm b) (monomialExp a : MvPolynomial (Fin N) R) = 0 := by
  simp only [monomialExp_eq_monomial, coeff, coeff_monomial, ite_eq_right_iff]
  intro heq
  exfalso
  apply h
  exact Finsupp.equivFunOnFinite.symm.injective heq

/-- The total degree of monomialExp a is the sum of entries of a (when nonzero). -/
lemma monomialExp_totalDegree [Nontrivial R] (a : Fin N → ℕ) :
    (monomialExp a : MvPolynomial (Fin N) R).totalDegree = ∑ i, a i := by
  rw [monomialExp_eq_monomial, MvPolynomial.totalDegree_monomial _ one_ne_zero]
  simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite_symm_apply_apply]

/-- monomialExp 0 is 1. -/
@[simp]
lemma monomialExp_zero : (monomialExp (0 : Fin N → ℕ) : MvPolynomial (Fin N) R) = 1 := by
  simp [monomialExp]

/-- monomialExp is multiplicative in the exponent. -/
lemma monomialExp_add (a b : Fin N → ℕ) :
    (monomialExp (a + b) : MvPolynomial (Fin N) R) = monomialExp a * monomialExp b := by
  simp only [monomialExp, Pi.add_apply, pow_add]
  rw [Finset.prod_mul_distrib]

/-- Sorting is idempotent: sorting an already sorted tuple gives the same tuple. -/
lemma sortTuple_idempotent (a : Fin N → ℕ) :
    sortTuple (sortTuple a).parts = sortTuple a :=
  sortTuple_of_NPartition (sortTuple a)


/-- Two tuples have the same sort if and only if one is a permutation of the other.
    (Two tuples have the same multiset of values iff they sort to the same N-partition.) -/
lemma sortTuple_eq_iff (a b : Fin N → ℕ) :
    sortTuple a = sortTuple b ↔
    (Finset.univ.val.map a) = (Finset.univ.val.map b) := by
  constructor
  · -- Forward: If sortTuple a = sortTuple b, then the multisets are equal
    intro h
    -- The sorted lists are equal (since NPartition.parts are equal)
    have h_parts : (sortTuple a).parts = (sortTuple b).parts := congrArg NPartition.parts h
    -- The sorted lists as multisets equal the original multisets
    have ha_sort : ↑((Finset.univ.val.map a).sort (· ≥ ·)) = Finset.univ.val.map a :=
      Multiset.sort_eq (r := (· ≥ ·)) (Finset.univ.val.map a)
    have hb_sort : ↑((Finset.univ.val.map b).sort (· ≥ ·)) = Finset.univ.val.map b :=
      Multiset.sort_eq (r := (· ≥ ·)) (Finset.univ.val.map b)
    -- We need to show the sorted lists are equal as lists
    have hlen_a : ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := sortTuple_sorted_length a
    have hlen_b : ((Finset.univ.val.map b).sort (· ≥ ·)).length = N := sortTuple_sorted_length b
    -- Extract the sorted lists
    let sorted_a := (Finset.univ.val.map a).sort (· ≥ ·)
    let sorted_b := (Finset.univ.val.map b).sort (· ≥ ·)
    -- Show sorted_a = sorted_b as lists
    have h_lists_eq : sorted_a = sorted_b := by
      apply List.ext_get
      · rw [hlen_a, hlen_b]
      · intro n h1 h2
        have hn_a : n < N := by rw [← hlen_a]; exact h1
        have hn_b : n < N := by rw [← hlen_b]; exact h2
        -- (sortTuple a).parts ⟨n, hn_a⟩ = sorted_a.get ⟨n, h1⟩
        have eq_a : (sortTuple a).parts ⟨n, hn_a⟩ = sorted_a.get ⟨n, h1⟩ := by
          simp only [sortTuple]
          rw [dif_pos h1]
        have eq_b : (sortTuple b).parts ⟨n, hn_b⟩ = sorted_b.get ⟨n, h2⟩ := by
          simp only [sortTuple]
          rw [dif_pos h2]
        rw [← eq_a, ← eq_b]
        exact congrFun h_parts ⟨n, hn_a⟩
    -- Now use that equal lists have equal multisets
    calc Finset.univ.val.map a = ↑sorted_a := ha_sort.symm
      _ = ↑sorted_b := by rw [h_lists_eq]
      _ = Finset.univ.val.map b := hb_sort
  · -- Backward: If multisets are equal, then sorting gives the same result
    intro h
    -- If the multisets are equal, sorting them gives the same sorted list
    have h_sorted_eq : (Finset.univ.val.map a).sort (· ≥ ·) = (Finset.univ.val.map b).sort (· ≥ ·) := by
      rw [h]
    -- Show parts are equal by showing the defining functions agree
    apply NPartition.ext
    funext i
    simp only [sortTuple]
    -- Use the fact that the sorted lists are equal
    have hlen_eq : ((Finset.univ.val.map a).sort (· ≥ ·)).length =
                   ((Finset.univ.val.map b).sort (· ≥ ·)).length := by
      rw [h_sorted_eq]
    split_ifs with ha hb hb
    · -- Both conditions hold: use that equal lists have equal elements
      simp only [List.get_eq_getElem, h_sorted_eq]
    · -- ha holds but hb doesn't - contradiction since lengths are equal
      rw [hlen_eq] at ha
      exact absurd ha hb
    · -- ha doesn't hold but hb does - contradiction since lengths are equal
      rw [← hlen_eq] at hb
      exact absurd hb ha
    · -- Neither condition holds
      rfl


/-- The product over a subset equals the product with indicator exponents. -/
lemma prod_subset_eq_prod_indicator (S : Finset (Fin N)) :
    (∏ i ∈ S, X i : MvPolynomial (Fin N) R) =
    ∏ j : Fin N, X j ^ (if j ∈ S then 1 else 0) := by
  conv_rhs =>
    arg 2
    ext j
    rw [show (X j : MvPolynomial (Fin N) R) ^ (if j ∈ S then 1 else 0) =
        if j ∈ S then X j else 1 by split_ifs <;> simp]
  rw [Finset.prod_ite (p := fun j => j ∈ S)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.prod_const_one, mul_one]

/-- The power X i ^ n equals the product with a single nonzero exponent. -/
lemma X_pow_eq_prod_single (i : Fin N) (n : ℕ) :
    (X i : MvPolynomial (Fin N) R) ^ n = ∏ j : Fin N, X j ^ (if j = i then n else 0) := by
  conv_rhs =>
    arg 2
    ext j
    rw [show (X j : MvPolynomial (Fin N) R) ^ (if j = i then n else 0) =
        if j = i then X j ^ n else 1 by split_ifs <;> simp]
  rw [Finset.prod_ite_eq' Finset.univ i (fun j => X j ^ n)]
  simp

/-- Multiset product as product over all elements with count exponents. -/
lemma multiset_prod_map_X_eq_prod_pow (s : Multiset (Fin N)) :
    (s.map (X : Fin N → MvPolynomial (Fin N) R)).prod =
    ∏ i : Fin N, X i ^ (Multiset.count i s) := by
  rw [Finset.prod_multiset_map_count s X]
  rw [← Finset.prod_subset (s.toFinset.subset_univ)]
  intro i _ hi
  simp only [Multiset.mem_toFinset] at hi
  rw [Multiset.count_eq_zero.mpr hi]
  simp

/-- The indicator tuple of an n-element subset sorts to onesThenZeros n. -/
lemma sortTuple_indicatorTuple {n : ℕ} (S : Finset (Fin N)) (hn : S.card = n) (hn' : n ≤ N) :
    sortTuple (indicatorTuple S) = onesThenZeros n hn' := by
  -- Key insight: Both indicatorTuple S and onesThenZeros.parts have the same multiset of values
  -- (n ones and N-n zeros), so they sort to the same result.
  -- Since onesThenZeros is already an NPartition (antitone), sorting it gives itself.
  rw [← sortTuple_of_NPartition (onesThenZeros n hn')]
  rw [sortTuple_eq_iff]
  -- Now we show the multisets are equal
  rw [Multiset.ext]
  intro v
  simp only [Multiset.count_map]
  -- `count_map` freezes a `DecidablePred` on `indicatorTuple`. Move to the `ite`
  -- spelling with `filter_congr` so later `rw`s see one instance.
  conv_lhs =>
    change (Finset.univ.filter (fun a : Fin N => v = indicatorTuple S a)).card
    rw [Finset.filter_congr (q := fun a : Fin N => v = if a ∈ S then 1 else 0)
      (fun a _ => by simp [indicatorTuple])]
  conv_rhs =>
    change (Finset.univ.filter (fun a : Fin N => v = (onesThenZeros n hn').parts a)).card
    rw [Finset.filter_congr (q := fun a : Fin N => v = if a.val < n then 1 else 0)
      (fun a _ => by simp [onesThenZeros])]
  by_cases hv0 : v = 0
  · -- Case v = 0: count is N - n for both
    subst hv0
    have h1 : (Finset.univ.filter (fun j : Fin N => 0 = (if j ∈ S then 1 else 0))) = Finset.univ \ S := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · intro h hj; rw [if_pos hj] at h; exact Nat.zero_ne_one h
      · intro hj; rw [if_neg hj]
    have h2 : (Finset.univ.filter (fun j : Fin N => 0 = (if j.val < n then 1 else 0))) =
              Finset.univ.filter (fun j : Fin N => n ≤ j.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; by_contra hj; push Not at hj; rw [if_pos hj] at h; exact Nat.zero_ne_one h
      · intro hj; rw [if_neg (not_lt.mpr hj)]
    have h3 : (Finset.univ.filter (fun j : Fin N => n ≤ j.val)).card = N - n := by
      have hbij : (Finset.univ.filter (fun j : Fin N => n ≤ j.val)) =
                  (Finset.univ : Finset (Fin (N - n))).map
                    ⟨fun k => ⟨k.val + n, Nat.add_lt_of_lt_sub k.isLt⟩,
                     fun a b h => by simp only [Fin.mk.injEq] at h; omega⟩ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.ext_iff]
        constructor
        · intro hj
          have hlt : j.val - n < N - n := Nat.sub_lt_sub_right hj j.isLt
          exact ⟨⟨j.val - n, hlt⟩, Nat.sub_add_cancel hj⟩
        · intro ⟨k, hk⟩
          rw [← hk]
          exact Nat.le_add_left n k.val
      rw [hbij, Finset.card_map, Finset.card_fin]
    rw [h1, h2, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hn, h3]
  · by_cases hv1 : v = 1
    · -- Case v = 1: count is n for both
      subst hv1
      have h1 : (Finset.univ.filter (fun j : Fin N => 1 = (if j ∈ S then 1 else 0))) = S := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; by_contra hj; rw [if_neg hj] at h; exact Nat.one_ne_zero h
        · intro hj; rw [if_pos hj]
      have h2 : (Finset.univ.filter (fun j : Fin N => 1 = (if j.val < n then 1 else 0))) =
                Finset.univ.filter (fun j : Fin N => j.val < n) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; by_contra hj; push Not at hj; rw [if_neg (not_lt.mpr hj)] at h; exact Nat.one_ne_zero h
        · intro hj; rw [if_pos hj]
      have h3 : (Finset.univ.filter (fun j : Fin N => j.val < n)).card = n := by
        have hbij : (Finset.univ.filter (fun j : Fin N => j.val < n)) =
                    (Finset.univ : Finset (Fin n)).map ⟨Fin.castLE hn', Fin.castLE_injective hn'⟩ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                     Function.Embedding.coeFn_mk]
          constructor
          · intro hj; exact ⟨⟨j.val, hj⟩, by simp [Fin.castLE]⟩
          · intro ⟨k, hk⟩; simp only [Fin.castLE, Fin.ext_iff] at hk; omega
        rw [hbij, Finset.card_map, Finset.card_fin]
      rw [h1, h2, hn, h3]
    · -- Case v ≠ 0 and v ≠ 1: both counts are 0
      have h1 : (Finset.univ.filter (fun j : Fin N => v = (if j ∈ S then 1 else 0))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j _; split_ifs with hj; exact hv1; exact hv0
      have h2 : (Finset.univ.filter (fun j : Fin N => v = (if j.val < n then 1 else 0))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j _; split_ifs with hj; exact hv1; exact hv0
      rw [h1, h2]

/-- The single tuple with n at position i sorts to singletonPartition n. -/
lemma sortTuple_singleTuple (i : Fin N) (n : ℕ) (hN : 0 < N) :
    sortTuple (singleTuple i n) = singletonPartition n hN := by
  -- Key insight: singleTuple i n = (singletonPartition n hN).parts ∘ (swap ⟨0, hN⟩ i)
  -- This is because singleTuple has n at position i and 0 elsewhere,
  -- while singletonPartition has n at position 0 and 0 elsewhere.
  -- The swap permutation maps 0 ↔ i, so composing gives the same values.
  have h_eq : singleTuple i n = (singletonPartition n hN).parts ∘ (Equiv.swap ⟨0, hN⟩ i) := by
    ext j
    simp only [singleTuple, singletonPartition, Function.comp_apply]
    by_cases hj : j = i
    · simp only [hj, ↓reduceIte, Equiv.swap_apply_right]
    · by_cases hj0 : j = ⟨0, hN⟩
      · simp only [hj0, Equiv.swap_apply_left]
        by_cases hi0 : i = ⟨0, hN⟩
        · exact absurd (hj0.trans hi0.symm) hj
        · have hi0_val : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          simp only [hi0_val, ↓reduceIte, Ne.symm hi0, ↓reduceIte]
      · simp only [hj, ↓reduceIte, Equiv.swap_apply_of_ne_of_ne hj0 hj]
        have hj_ne_0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        simp only [hj_ne_0, ↓reduceIte]
  rw [h_eq, sortTuple_comp_perm, sortTuple_of_NPartition]

/-- The count tuple sorts to an N-partition of size n. -/
lemma sortTuple_countTuple_size {n : ℕ} (s : Sym (Fin N) n) :
    (sortTuple (countTuple s)).size = n := by
  rw [sortTuple_size]
  simp only [countTuple]
  -- Sum of counts equals card of multiset
  have h : ∑ i : Fin N, Multiset.count i s.1 = s.1.card := by
    rw [← Multiset.toFinset_sum_count_eq s.1]
    symm
    apply Finset.sum_subset s.1.toFinset.subset_univ
    intro i _ hi
    simp only [Multiset.mem_toFinset] at hi
    exact Multiset.count_eq_zero.mpr hi
  rw [h, s.2]

/-- Indicator tuple is in sortPreimage of onesThenZeros. -/
lemma indicatorTuple_mem_sortPreimage {n : ℕ} (S : Finset (Fin N)) (hn : S.card = n) (hn' : n ≤ N) :
    indicatorTuple S ∈ sortPreimage (onesThenZeros n hn') := by
  simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · intro i
    simp only [indicatorTuple, onesThenZeros, NPartition.size]
    -- The size of onesThenZeros n is n (sum of n ones)
    -- Each entry of indicatorTuple is 0 or 1, so < n + 1
    -- First, compute the sum: ∑ j, if j.val < n then 1 else 0 = n
    have hsum : ∑ j : Fin N, (if j.val < n then 1 else 0) = n := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      have : (Finset.univ.filter (fun j : Fin N => j.val < n)) =
             (Finset.univ : Finset (Fin n)).map ⟨Fin.castLE hn', Fin.castLE_injective hn'⟩ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                   Function.Embedding.coeFn_mk]
        constructor
        · intro hj
          exact ⟨⟨j.val, hj⟩, by simp [Fin.castLE]⟩
        · intro ⟨k, hk⟩
          simp only [Fin.castLE, Fin.ext_iff] at hk
          omega
      rw [this, Finset.card_map, Finset.card_fin]
    rw [hsum]
    -- Now goal is: (if i ∈ S then 1 else 0) < n + 1
    split_ifs with hi
    · -- i ∈ S, indicator is 1, need 1 < n + 1
      have : S.Nonempty := ⟨i, hi⟩
      have : 0 < S.card := Finset.card_pos.mpr this
      omega
    · -- i ∉ S, indicator is 0, need 0 < n + 1
      omega
  · exact sortTuple_indicatorTuple S hn hn'

/-- Single tuple is in sortPreimage of singletonPartition. -/
lemma singleTuple_mem_sortPreimage (i : Fin N) (n : ℕ) (hN : 0 < N) :
    singleTuple i n ∈ sortPreimage (singletonPartition n hN) := by
  simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · intro j
    -- The size of singletonPartition n is n
    -- Each entry of singleTuple is 0 or n, so < n + 1
    simp only [NPartition.size, singletonPartition, singleTuple]
    have hsize : ∑ k : Fin N, (if k.val = 0 then n else 0) = n := by
      conv_lhs => arg 2; ext k; rw [show (if k.val = 0 then n else 0) =
                                        if k = ⟨0, hN⟩ then n else 0 by simp [Fin.ext_iff]]
      simp [Finset.sum_ite_eq']
    rw [hsize]
    split_ifs <;> omega
  · exact sortTuple_singleTuple i n hN

/-- monomialExp of singleTuple i n equals X i ^ n.
    This is a key helper for `power_sum_eq_monomialSymm`. -/
lemma monomialExp_singleTuple (i : Fin N) (n : ℕ) :
    (monomialExp (singleTuple i n) : MvPolynomial (Fin N) R) = X i ^ n := by
  simp only [monomialExp, singleTuple]
  conv_lhs =>
    arg 2
    ext j
    rw [show (X j : MvPolynomial (Fin N) R) ^ (if j = i then n else 0) =
        if j = i then X j ^ n else 1 by
      split_ifs with h <;> simp [h]]
  simp [Finset.prod_ite_eq']

/-- Values in sortPreimage of singletonPartition are either 0 or n.
    This follows because sortTuple preserves multisets, and singletonPartition has only 0s and one n. -/
lemma sortPreimage_singletonPartition_values (a : Fin N → ℕ) (n : ℕ) (hN : 0 < N)
    (ha : a ∈ sortPreimage (singletonPartition n hN)) (i : Fin N) :
    a i = 0 ∨ a i = n := by
  simp only [sortPreimage, Finset.mem_filter] at ha
  -- sortTuple a = singletonPartition n means the multisets are equal
  have hmulti : Finset.univ.val.map a = Finset.univ.val.map (singletonPartition n hN).parts := by
    rw [← sortTuple_eq_iff]
    rw [ha.2, sortTuple_of_NPartition]
  -- From hmulti, we know a i is in the multiset of singletonPartition values
  have hmem : a i ∈ Finset.univ.val.map (singletonPartition n hN).parts := by
    rw [← hmulti]
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, singletonPartition] at hmem
  obtain ⟨j, hj⟩ := hmem
  by_cases hj0 : j.val = 0
  · simp only [if_pos hj0] at hj
    right; exact hj.symm
  · simp only [if_neg hj0] at hj
    left; exact hj.symm

/-- If a ∈ sortPreimage (singletonPartition n hN) and n > 0, then a = singleTuple i n for some i. -/
lemma mem_sortPreimage_singletonPartition_exists_singleTuple (a : Fin N → ℕ) (n : ℕ) (hn : n ≠ 0) (hN : 0 < N)
    (ha : a ∈ sortPreimage (singletonPartition n hN)) :
    ∃ i, a = singleTuple i n := by
  -- The sum of a equals n (since sortTuple preserves sum and singletonPartition has size n)
  have hsum : ∑ j, a j = n := by
    have h1 := sortTuple_sum_eq a
    simp only [sortPreimage, Finset.mem_filter] at ha
    rw [ha.2] at h1
    simp only [singletonPartition] at h1
    convert h1.symm
    conv_rhs => arg 2; ext k; rw [show (if k.val = 0 then n else 0) =
                                      if k = ⟨0, hN⟩ then n else 0 by simp [Fin.ext_iff]]
    simp [Finset.sum_ite_eq']
  -- Since all values are 0 or n and sum is n, exactly one value is n
  -- Find an index with value n
  have hexists : ∃ i, a i = n := by
    by_contra hall
    push Not at hall
    -- If all values are 0 or n but none is n, all are 0
    have hall0 : ∀ i, a i = 0 := by
      intro i
      rcases sortPreimage_singletonPartition_values a n hN ha i with h0 | hn'
      · exact h0
      · exact absurd hn' (hall i)
    -- But sum is n > 0, contradiction
    simp only [hall0, Finset.sum_const_zero] at hsum
    exact hn hsum.symm
  obtain ⟨i, hi⟩ := hexists
  use i
  ext j
  simp only [singleTuple]
  by_cases hji : j = i
  · simp [hji, hi]
  · simp only [hji, ↓reduceIte]
    -- j ≠ i, and a j is either 0 or n
    rcases sortPreimage_singletonPartition_values a n hN ha j with h0 | hn'
    · exact h0
    · -- If a j = n and a i = n with j ≠ i, then sum ≥ 2n > n (contradiction)
      exfalso
      have h2n : a i + a j ≤ ∑ k, a k := by
        have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
        calc a i + a j = ∑ k ∈ ({i, j} : Finset (Fin N)), a k := by
               simp [Finset.sum_pair (Ne.symm hji)]
             _ ≤ ∑ k, a k := Finset.sum_le_sum_of_subset hsub
      rw [hi, hn', hsum] at h2n
      omega

/-- indicatorSupport ∘ indicatorTuple = id -/
lemma indicatorSupport_indicatorTuple (S : Finset (Fin N)) :
    indicatorSupport (indicatorTuple S) = S := by
  ext i
  simp only [indicatorSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [indicatorTuple]
  constructor
  · intro h
    by_contra hne
    rw [if_neg hne] at h
    exact Nat.one_ne_zero h.symm
  · intro h
    rw [if_pos h]

/-- Values in sortPreimage of onesThenZeros are in {0, 1}.
    This follows because sortTuple preserves multisets, and onesThenZeros has only 0s and 1s. -/
lemma sortPreimage_onesThenZeros_values {n : ℕ} (a : Fin N → ℕ) (hn' : n ≤ N)
    (ha : a ∈ sortPreimage (onesThenZeros n hn')) (i : Fin N) :
    a i = 0 ∨ a i = 1 := by
  simp only [sortPreimage, Finset.mem_filter] at ha
  -- sortTuple a = onesThenZeros n means the multisets are equal
  have hmulti : Finset.univ.val.map a = Finset.univ.val.map (onesThenZeros n hn').parts := by
    rw [← sortTuple_eq_iff]
    rw [ha.2, sortTuple_of_NPartition]
  -- From hmulti, we know a i is in the multiset of onesThenZeros values
  have hmem : a i ∈ Finset.univ.val.map (onesThenZeros n hn').parts := by
    rw [← hmulti]
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, onesThenZeros] at hmem
  obtain ⟨j, hj⟩ := hmem
  by_cases hjn : j.val < n
  · simp only [if_pos hjn] at hj
    right; exact hj.symm
  · simp only [if_neg hjn] at hj
    left; exact hj.symm

/-- indicatorTuple ∘ indicatorSupport = id for elements of sortPreimage of onesThenZeros. -/
lemma indicatorTuple_indicatorSupport {n : ℕ} (a : Fin N → ℕ) (hn' : n ≤ N)
    (ha : a ∈ sortPreimage (onesThenZeros n hn')) :
    indicatorTuple (indicatorSupport a) = a := by
  ext i
  simp only [indicatorTuple, indicatorSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases sortPreimage_onesThenZeros_values a hn' ha i with h0 | h1
  · simp [h0]
  · simp [h1]

/-- The cardinality of indicatorSupport for elements of sortPreimage of onesThenZeros equals n. -/
lemma indicatorSupport_card {n : ℕ} (a : Fin N → ℕ) (hn' : n ≤ N)
    (ha : a ∈ sortPreimage (onesThenZeros n hn')) :
    (indicatorSupport a).card = n := by
  simp only [sortPreimage, Finset.mem_filter] at ha
  -- The sum of a equals n
  have hsum : ∑ i, a i = n := by
    calc ∑ i, a i = (sortTuple a).size := (sortTuple_size a).symm
      _ = (onesThenZeros n hn').size := by rw [ha.2]
      _ = n := by
        simp only [NPartition.size, onesThenZeros]
        rw [Finset.sum_boole]
        simp only [Nat.cast_id]
        have : (Finset.univ.filter (fun j : Fin N => j.val < n)) =
               (Finset.univ : Finset (Fin n)).map ⟨Fin.castLE hn', Fin.castLE_injective hn'⟩ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                     Function.Embedding.coeFn_mk]
          constructor
          · intro hj; exact ⟨⟨j.val, hj⟩, by simp [Fin.castLE]⟩
          · intro ⟨k, hk⟩; simp only [Fin.castLE, Fin.ext_iff] at hk; omega
        rw [this, Finset.card_map, Finset.card_fin]
  -- Since a has values in {0, 1}, the sum equals the cardinality of indicatorSupport
  have ha' : a ∈ sortPreimage (onesThenZeros n hn') := by
    simp only [sortPreimage, Finset.mem_filter]
    exact ha
  have h : ∑ i, a i = (indicatorSupport a).card := by
    simp only [indicatorSupport, Finset.card_filter]
    rw [Finset.sum_congr rfl]
    intro i _
    rcases sortPreimage_onesThenZeros_values a hn' ha' i with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [← h, hsum]

/-- The product over a subset equals monomialExp of the indicator tuple. -/
lemma prod_subset_eq_monomialExp (S : Finset (Fin N)) :
    (∏ i ∈ S, X i : MvPolynomial (Fin N) R) = monomialExp (indicatorTuple S) := by
  simp only [monomialExp, indicatorTuple]
  rw [prod_subset_eq_prod_indicator]

/-- e_n = m_{(1,1,...,1,0,0,...,0)} where there are n ones.
    (Proposition prop.sf.ehp-through-m (a))

    The proof uses the fact that esymm n is the sum over n-element subsets S of ∏_{i∈S} X_i,
    and each such product equals X^{χ_S} where χ_S is the indicator function of S.
    All indicator functions of n-element subsets sort to the same N-partition (1,...,1,0,...,0).

    Label: prop.sf.ehp-through-m.a -/
lemma elem_symm_eq_monomialSymm [DecidableEq (Fin N)] (n : ℕ) (hn : n ≤ N) :
    esymm (Fin N) R n = monomialSymm (onesThenZeros n hn) := by
  -- esymm n = ∑_{S : |S| = n} ∏_{i ∈ S} X_i
  -- monomialSymm (1,...,1,0,...,0) = ∑_{a : sort(a) = (1,...,1,0,...,0)} X^a
  simp only [esymm, monomialSymm]
  -- Use sum_bij' to establish a bijection between powersetCard n univ and sortPreimage
  apply Finset.sum_bij' (fun S _ => indicatorTuple S) (fun a _ => indicatorSupport a)
  -- indicatorTuple maps to sortPreimage
  · intro S hS
    have hcard : S.card = n := Finset.mem_powersetCard.mp hS |>.2
    exact indicatorTuple_mem_sortPreimage S hcard hn
  -- indicatorSupport maps to powersetCard
  · intro a ha
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, indicatorSupport_card a hn ha⟩
  -- Left inverse: indicatorSupport ∘ indicatorTuple = id
  · intro S _
    exact indicatorSupport_indicatorTuple S
  -- Right inverse: indicatorTuple ∘ indicatorSupport = id
  · intro a ha
    exact indicatorTuple_indicatorSupport a hn ha
  -- The terms match: ∏ i ∈ S, X i = monomialExp (indicatorTuple S)
  · intro S _
    exact prod_subset_eq_monomialExp S

/-- The set of N-partitions of size n is finite (set version).
    This is the Set.Finite version of fintype_of_size. -/
lemma finite_of_size (n : ℕ) : Set.Finite { μ : NPartition N | μ.size = n } := by
  haveI : Fintype { μ : NPartition N // μ.size = n } := fintype_of_size n
  haveI : Finite { μ : NPartition N // μ.size = n } := Finite.of_fintype _
  exact Set.finite_coe_iff.mp this

/-- h_n = ∑_{|μ| = n} m_μ where the sum is over N-partitions of size n.
    (Proposition prop.sf.ehp-through-m (b))

    The proof uses the bijection between Sym (Fin N) n and tuples f : Fin N → ℕ with ∑ f = n,
    given by the count function. Each term (s.1.map X).prod = ∏ i, X i ^ (count i s)
    corresponds to a monomial X^f. Sorting partitions these tuples by their N-partition,
    so hsymm n = ∑_{|μ| = n} m_μ.

    Label: prop.sf.ehp-through-m.b -/
lemma homog_symm_eq_sum_monomialSymm [DecidableEq (Fin N)] (n : ℕ) :
    hsymm (Fin N) R n = ∑ mu ∈ NPartitionsOfSize n, monomialSymm mu := by
  -- hsymm n = ∑_{s : Sym (Fin N) n} (s.1.map X).prod
  --         = ∑_{s : Sym (Fin N) n} ∏ i, X i ^ (count i s)
  --         = ∑_{f : ∑ f = n} X^f
  --         = ∑_{|μ| = n} ∑_{sort(f) = μ} X^f
  --         = ∑_{|μ| = n} m_μ
  -- Step 1: Rewrite hsymm and transform each term to monomialExp
  simp only [hsymm]
  conv_lhs =>
    arg 2
    ext s
    rw [show (s.1.map X : Multiset (MvPolynomial (Fin N) R)).prod = monomialExp (fun i => s.1.count i) by
      simp only [monomialExp]
      rw [Finset.prod_multiset_map_count]
      -- Need to show: ∏ m ∈ s.1.toFinset, X m ^ count m s.1 = ∏ i, X i ^ count i s.1
      -- The RHS is over all of Fin N, the LHS is only over elements in s.1
      -- But for elements not in s.1, count is 0, so X i ^ 0 = 1
      apply Finset.prod_subset s.1.toFinset.subset_univ
      intro i _ hi
      simp only [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_zero.mpr hi, pow_zero]]
  -- Step 2: Use the bijection between Sym (Fin N) n and piAntidiag univ n
  have huniv : (Finset.univ : Finset (Fin N)).sym n = Finset.univ := by ext s; simp
  let countEmbed : Sym (Fin N) n ↪ (Fin N → ℕ) :=
    ⟨fun m a => m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩
  have hmap : Finset.map countEmbed ((Finset.univ : Finset (Fin N)).sym n) =
              Finset.piAntidiag Finset.univ n :=
    Finset.map_sym_eq_piAntidiag (Finset.univ : Finset (Fin N)) n
  -- Step 3: Transform sum over Sym to sum over piAntidiag
  have h_sym_to_piAntidiag : ∑ s : Sym (Fin N) n, (monomialExp (fun i => s.1.count i) : MvPolynomial (Fin N) R) =
            ∑ f ∈ Finset.piAntidiag Finset.univ n, monomialExp f := by
    calc ∑ s : Sym (Fin N) n, (monomialExp (fun i => s.1.count i) : MvPolynomial (Fin N) R)
        = ∑ s : Sym (Fin N) n, monomialExp (countEmbed s) := rfl
      _ = ∑ s ∈ Finset.univ, monomialExp (countEmbed s) := rfl
      _ = ∑ s ∈ (Finset.univ : Finset (Fin N)).sym n, monomialExp (countEmbed s) := by rw [huniv]
      _ = ∑ f ∈ ((Finset.univ : Finset (Fin N)).sym n).map countEmbed, monomialExp f := by rw [Finset.sum_map]
      _ = ∑ f ∈ Finset.piAntidiag Finset.univ n, monomialExp f := by rw [hmap]
  rw [h_sym_to_piAntidiag]
  -- Step 4: Partition piAntidiag by sortTuple
  -- The sortPreimages are pairwise disjoint
  have h_disjoint : (↑(NPartitionsOfSize (N := N) n) : Set (NPartition N)).PairwiseDisjoint sortPreimage := by
    intro mu _ nu _ hne
    simp only [Function.onFun, Finset.disjoint_iff_ne]
    intro f hf g hg heq
    simp only [sortPreimage, Finset.mem_filter] at hf hg
    rw [heq] at hf
    exact hne (hf.2.symm.trans hg.2)
  -- piAntidiag univ n = disjoint union of sortPreimage mu over NPartitionsOfSize n
  have h_partition : Finset.piAntidiag (Finset.univ : Finset (Fin N)) n =
      (NPartitionsOfSize n).biUnion sortPreimage := by
    ext f
    simp only [Finset.mem_piAntidiag, Finset.mem_biUnion, ne_eq]
    constructor
    · intro ⟨hsum, _⟩
      let mu := sortTuple f
      use mu
      constructor
      · simp only [NPartitionsOfSize, Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset,
          Finset.mem_range]
        constructor
        · refine ⟨f, ?_, rfl⟩
          intro i
          have h1 : f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          linarith
        · rw [sortTuple_size, hsum]
      · simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        constructor
        · intro i
          have hmu_size : mu.size = n := by rw [sortTuple_size, hsum]
          have h1 : f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          linarith
        · rfl
    · intro ⟨mu, hmu, hf⟩
      simp only [NPartitionsOfSize, Finset.mem_filter] at hmu
      simp only [sortPreimage, Finset.mem_filter] at hf
      constructor
      · calc ∑ i, f i = (sortTuple f).size := (sortTuple_size f).symm
          _ = mu.size := by rw [hf.2]
          _ = n := hmu.2
      · intro i _; exact Finset.mem_univ i
  -- Step 5: Conclude
  rw [h_partition, Finset.sum_biUnion h_disjoint]
  rfl

/-- p_n = m_{(n,0,0,...,0)} when N > 0 and n > 0.
    (Proposition prop.sf.ehp-through-m (c))

    **Important**: This theorem requires `n > 0`. The case `n = 0` is FALSE when `N > 1`:
    - `psum 0 = ∑ i, X i ^ 0 = N` (the constant polynomial N)
    - `monomialSymm (singletonPartition 0 hN) = 1` (since the only tuple sorting to
      (0,...,0) is the zero tuple, and `monomialExp (0,...,0) = 1`)

    The TeX source (MonomialSymmetric.tex, line 133) states "For each n ∈ ℕ, we have
    p_n = m_{(n,0,0,...,0)}" which is mathematically incorrect for n = 0 when N > 1.

    The proof uses the fact that psum n = ∑ i, X i ^ n, and each term X i ^ n
    corresponds to the tuple (0,...,0,n,0,...,0) with n at position i.
    All N such tuples sort to the same N-partition (n, 0, 0, ..., 0).

    When n > 0, the sortPreimage of (n, 0, ..., 0) consists exactly of the N single
    tuples (0,...,0,n,0,...,0), giving the bijection needed for the proof.

    Label: prop.sf.ehp-through-m.c -/
lemma power_sum_eq_monomialSymm [DecidableEq (Fin N)] (n : ℕ) (hn : n ≠ 0) (hN : 0 < N) :
    psum (Fin N) R n = monomialSymm (singletonPartition n hN) := by
  -- psum n = ∑ i, X i ^ n
  --        = ∑ i, ∏ j, X j ^ (if j = i then n else 0)
  --        = ∑ i, monomialExp (singleTuple i n)
  -- The sortPreimage of (n, 0, ..., 0) consists exactly of the N single tuples
  -- So monomialSymm (n, 0, ..., 0) = ∑_{a ∈ sortPreimage} monomialExp a = ∑ i, monomialExp (singleTuple i n)
  simp only [psum, monomialSymm]
  -- Rewrite LHS using monomialExp_singleTuple
  conv_lhs =>
    arg 2
    ext i
    rw [← monomialExp_singleTuple (R := R) i n]
  -- Now goal is: ∑ i, monomialExp (singleTuple i n) = ∑ a ∈ sortPreimage ..., monomialExp a
  -- Use Finset.sum_bij to establish the bijection
  apply Finset.sum_bij (fun i _ => singleTuple i n)
  · -- singleTuple i n ∈ sortPreimage (singletonPartition n hN)
    intro i _
    exact singleTuple_mem_sortPreimage i n hN
  · -- Injectivity: singleTuple i n = singleTuple j n implies i = j
    intro i _ j _ hij
    by_contra hne
    -- singleTuple i n at position i is n, but singleTuple j n at position i is 0 (since i ≠ j)
    have h1 : singleTuple i n i = n := by simp [singleTuple]
    have h2 : singleTuple j n i = 0 := by simp [singleTuple, hne]
    rw [hij] at h1
    rw [h1] at h2
    exact hn h2
  · -- Surjectivity: every a ∈ sortPreimage is singleTuple i n for some i
    intro a ha
    obtain ⟨i, hi⟩ := mem_sortPreimage_singletonPartition_exists_singleTuple a n hn hN ha
    exact ⟨i, Finset.mem_univ i, hi.symm⟩
  · -- The function values are equal (trivially true since we're applying the same function)
    intro i _
    rfl

/-- The n = 0 case: p_0 = N while m_{(0,...,0)} = 1.

    This documents why `power_sum_eq_monomialSymm` requires `n ≠ 0`.
    When n = 0:
    - `psum 0 = ∑ i, X i ^ 0 = N` (constant polynomial)
    - `monomialSymm (singletonPartition 0 hN) = 1` (single monomial x^0 = 1)

    These are equal only when N = 1. -/
lemma psum_zero_eq_N : psum (Fin N) R 0 = N := by
  simp only [psum, pow_zero, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]

lemma monomialSymm_zero_partition_eq_one (hN : 0 < N) :
    monomialSymm (R := R) (singletonPartition 0 hN) = 1 := by
  -- The zero partition (0, 0, ..., 0) has sortPreimage = {(0, 0, ..., 0)}
  -- and monomialExp (0, ..., 0) = x^0 = 1
  -- Proof outline:
  -- 1. sortPreimage of (0,...,0) contains only the zero tuple because:
  --    - The size of (0,...,0) is 0
  --    - Each entry a_j must satisfy a_j < 0 + 1 = 1, so a_j = 0
  -- 2. monomialExp (0,...,0) = ∏_j X_j^0 = 1
  -- Step 1: singletonPartition 0 hN = 0
  have h_eq_zero : singletonPartition 0 hN = (0 : NPartition N) := by
    ext i
    simp only [singletonPartition, NPartition.zero_parts]
    simp
  rw [h_eq_zero]
  -- Step 2: sortPreimage 0 = {0}
  have h_sortTuple_zero : sortTuple (0 : Fin N → ℕ) = (0 : NPartition N) := by
    ext i
    simp only [sortTuple, NPartition.zero_parts, Pi.zero_apply]
    split_ifs with h
    · have hsorted_mem : ∀ x ∈ (Finset.univ.val.map (0 : Fin N → ℕ)).sort (· ≥ ·), x = 0 := by
        intro x hx
        rw [Multiset.mem_sort] at hx
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Pi.zero_apply] at hx
        obtain ⟨_, rfl⟩ := hx
        rfl
      exact hsorted_mem _ (List.get_mem _ ⟨i.val, h⟩)
    · rfl
  have h_preimage : sortPreimage (0 : NPartition N) = {0} := by
    ext a
    simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro ⟨ha_range, _⟩
      ext i
      specialize ha_range i
      simp only [NPartition.zero_size, Finset.mem_range] at ha_range
      simp only [Pi.zero_apply]
      omega
    · intro ha
      constructor
      · intro i
        rw [ha, NPartition.zero_size, Pi.zero_apply]
        simp
      · rw [ha]
        exact h_sortTuple_zero
  -- Step 3: monomialSymm 0 = monomialExp 0 = 1
  simp only [monomialSymm, h_preimage, Finset.sum_singleton]
  exact monomialExp_zero


/-- The coefficient of a monomial in σ · f equals the coefficient of the permuted
    monomial in f.
    (Proposition prop.sf.sigma-pol-coeff)

    [x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N}](σ · f) = [x₁^{a_{σ(1)}} x₂^{a_{σ(2)}} ⋯ x_N^{a_{σ(N)}}] f

    Label: prop.sf.sigma-pol-coeff -/
lemma sigma_coeff_permute (sigma : Perm (Fin N)) (f : MvPolynomial (Fin N) R)
    (a : Fin N → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm a) (rename sigma f) =
    coeff (Finsupp.equivFunOnFinite.symm (a ∘ sigma)) f := by
  have hmap : (Finsupp.equivFunOnFinite.symm (a ∘ sigma)).mapDomain (sigma : Fin N → Fin N) =
      Finsupp.equivFunOnFinite.symm a := by
    ext i
    rw [Finsupp.mapDomain_equiv_apply]
    simp [Finsupp.equivFunOnFinite_symm_apply_apply, Function.comp_apply]
  rw [← hmap]
  exact coeff_rename_mapDomain sigma sigma.injective f
    (Finsupp.equivFunOnFinite.symm (a ∘ sigma))


/-- The monomial symmetric polynomials are linearly independent.
    (Theorem thm.sf.m-basis (a), linear independence part)

    Label: thm.sf.m-basis.a.indep -/
lemma monomialSymm_linearIndependent (S : Finset (NPartition N)) :
    LinearIndependent R (fun mu : S => (monomialSymm mu.val : MvPolynomial (Fin N) R)) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg mu
  -- Extract the coefficient of mu.parts from the sum
  have key : coeff (Finsupp.equivFunOnFinite.symm mu.val.parts)
      (∑ nu : S, f nu • monomialSymm nu.val : MvPolynomial (Fin N) R) =
      coeff (Finsupp.equivFunOnFinite.symm mu.val.parts)
      (∑ nu : S, g nu • monomialSymm nu.val : MvPolynomial (Fin N) R) := by
    rw [hfg]
  simp only [coeff_sum, coeff_smul] at key
  -- The sum simplifies because only the term with nu = mu contributes
  have hf : ∑ nu : S, f nu • coeff (Finsupp.equivFunOnFinite.symm mu.val.parts)
      (monomialSymm nu.val : MvPolynomial (Fin N) R) = f mu := by
    rw [Finset.sum_eq_single_of_mem mu (Finset.mem_univ mu)]
    · simp [monomialSymm_coeff_self]
    · intro nu _ hne
      simp only [smul_eq_mul]
      have hne' : mu.val ≠ nu.val := fun heq => hne (Subtype.ext heq.symm)
      rw [monomialSymm_coeff_ne mu.val nu.val hne', mul_zero]
  have hg : ∑ nu : S, g nu • coeff (Finsupp.equivFunOnFinite.symm mu.val.parts)
      (monomialSymm nu.val : MvPolynomial (Fin N) R) = g mu := by
    rw [Finset.sum_eq_single_of_mem mu (Finset.mem_univ mu)]
    · simp [monomialSymm_coeff_self]
    · intro nu _ hne
      simp only [smul_eq_mul]
      have hne' : mu.val ≠ nu.val := fun heq => hne (Subtype.ext heq.symm)
      rw [monomialSymm_coeff_ne mu.val nu.val hne', mul_zero]
  rw [hf, hg] at key
  exact key

/-- For symmetric f, support is closed under permutation. -/
lemma support_closed_under_perm (f : MvPolynomial (Fin N) R) (hf : f.IsSymmetric)
    (d : Fin N →₀ ℕ) (hd : d ∈ f.support) (σ : Perm (Fin N)) :
    Finsupp.mapDomain σ d ∈ f.support := by
  rw [mem_support_iff] at hd ⊢
  simpa [coeff_perm_eq_of_symmetric f hf d σ] using hd

/-- sortTupleFinsupp is invariant under permutation. -/
lemma sortTupleFinsupp_perm (d : Fin N →₀ ℕ) (σ : Perm (Fin N)) :
    sortTupleFinsupp (Finsupp.mapDomain σ d) = sortTupleFinsupp d := by
  unfold sortTupleFinsupp
  have h : Finsupp.equivFunOnFinite (Finsupp.mapDomain σ d) =
           (Finsupp.equivFunOnFinite d) ∘ σ.symm := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  rw [h, sortTuple_comp_perm]


/-- Any symmetric polynomial f can be written as
    f = ∑_μ ([x₁^{μ₁} x₂^{μ₂} ⋯ x_N^{μ_N}] f) m_μ
    (Theorem thm.sf.m-basis (b))

    Label: thm.sf.m-basis.b -/
lemma symm_eq_sum_coeff_monomialSymm (f : MvPolynomial (Fin N) R) (hf : f.IsSymmetric)
    (S : Finset (NPartition N)) (hS : ∀ mu : NPartition N, mu.size ≤ f.totalDegree → mu ∈ S) :
    f = ∑ mu ∈ S, (coeff (Finsupp.equivFunOnFinite.symm mu.parts) f) • monomialSymm mu := by
  -- Helper: sortTupleFinsupp_parts
  have sortTupleFinsupp_parts : ∀ mu : NPartition N,
      sortTupleFinsupp (Finsupp.equivFunOnFinite.symm mu.parts) = mu := fun mu => by
    unfold sortTupleFinsupp
    simp only [Equiv.apply_symm_apply]
    exact sortTuple_of_NPartition mu
  -- Helper: sortTupleFinsupp_size
  have sortTupleFinsupp_size : ∀ d : Fin N →₀ ℕ,
      (sortTupleFinsupp d).size = d.sum (fun _ n => n) := fun d => by
    unfold sortTupleFinsupp
    rw [sortTuple_size]
    simp only [Finsupp.sum]
    have h : ∀ i : Fin N, Finsupp.equivFunOnFinite d i = d i := fun i => rfl
    simp_rw [h]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hx
    exact hx
  -- Helper: monomialSymm_coeff for general d
  have monomialSymm_coeff : ∀ (d : Fin N →₀ ℕ) (mu : NPartition N),
      coeff d (monomialSymm mu : MvPolynomial (Fin N) R) =
      if sortTupleFinsupp d = mu then 1 else 0 := fun d mu => by
    split_ifs with h
    · have hsort : sortTupleFinsupp d = sortTupleFinsupp (Finsupp.equivFunOnFinite.symm mu.parts) := by
        rw [h, sortTupleFinsupp_parts]
      have hcoeff := coeff_eq_of_same_sort (monomialSymm (R := R) mu) (monomialSymm_isSymmetric mu) d
          (Finsupp.equivFunOnFinite.symm mu.parts) hsort
      rw [hcoeff]
      exact monomialSymm_coeff_self mu
    · let nu := sortTupleFinsupp d
      have hnu : sortTupleFinsupp d = nu := rfl
      have hsort : sortTupleFinsupp d = sortTupleFinsupp (Finsupp.equivFunOnFinite.symm nu.parts) := by
        rw [hnu, sortTupleFinsupp_parts]
      have hcoeff := coeff_eq_of_same_sort (monomialSymm (R := R) mu) (monomialSymm_isSymmetric mu) d
          (Finsupp.equivFunOnFinite.symm nu.parts) hsort
      rw [hcoeff]
      exact monomialSymm_coeff_ne nu mu (fun heq => h (hnu.trans heq))
  -- Main proof: show both sides have the same coefficient for each exponent d
  ext1 d
  rw [coeff_sum]
  simp only [coeff_smul, smul_eq_mul]
  simp_rw [monomialSymm_coeff d]
  simp only [mul_ite, mul_one, mul_zero]
  let mu := sortTupleFinsupp d
  by_cases hmu : mu ∈ S
  · -- Case: μ ∈ S - the sum has exactly one nonzero term
    rw [Finset.sum_eq_single_of_mem mu hmu]
    · -- The term for μ gives the coefficient of d in f
      simp only [mu, ↓reduceIte]
      have hsort : sortTupleFinsupp d = sortTupleFinsupp (Finsupp.equivFunOnFinite.symm (sortTupleFinsupp d).parts) := by
        rw [sortTupleFinsupp_parts]
      exact coeff_eq_of_same_sort f hf d (Finsupp.equivFunOnFinite.symm (sortTupleFinsupp d).parts) hsort
    · -- All other terms are zero
      intro nu _ hne
      simp only [ite_eq_right_iff]
      intro heq
      exact absurd heq (Ne.symm hne)
  · -- Case: μ ∉ S - the coefficient must be 0
    -- First show the sum is 0
    have hsum_zero : ∑ x ∈ S, (if sortTupleFinsupp d = x then coeff (Finsupp.equivFunOnFinite.symm x.parts) f else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro nu hnu
      simp only [ite_eq_right_iff]
      intro heq
      exfalso
      have : mu = nu := heq
      rw [this] at hmu
      exact hmu hnu
    rw [hsum_zero]
    -- Show coeff d f = 0 by contradiction
    by_contra hcoeff_ne
    have hd_mem : d ∈ f.support := by rwa [mem_support_iff]
    have hdeg : d.sum (fun _ n => n) ≤ f.totalDegree := le_totalDegree hd_mem
    have hmu_size : mu.size = d.sum (fun _ n => n) := sortTupleFinsupp_size d
    have : mu.size ≤ f.totalDegree := by omega
    exact hmu (hS mu this)


end SymmetricFunctions

end AlgebraicCombinatorics
end


/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_coeff_rename_mapDomain
  [CommSemiring R]
-- given
  (f : σ → τ)
  (hf : Function.Injective f)
  (φ : MvPolynomial σ R)
  (d : Finsupp σ ℕ) :
-- imply
  coeff (d.mapDomain f) (rename f φ) = coeff d φ := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.coeff_rename_mapDomain f hf φ d

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_ofPartition_size
  {n : ℕ}
-- given
  (p : Nat.Partition n)
  (hp : Multiset.card p.parts ≤ N) :
-- imply
  (ofPartition p hp).size = n := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.ofPartition_size p hp

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_toPartition_card_le
-- given
  (mu : NPartition N) :
-- imply
  Multiset.card mu.toPartition.parts ≤ N := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.toPartition_card_le mu

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_parts_cast
  {m n : ℕ}
-- given
  (h : m = n)
  (p : Nat.Partition m) :
-- imply
  (h ▸ p).parts = p.parts := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.Nat.Partition.parts_cast h p

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_ofPartition_injective
-- given
  (n : ℕ) :
-- imply
  Function.Injective (fun x : Subtype (fun (p : Nat.Partition n) => Multiset.card p.parts ≤ N) => ofPartition x.val x.property) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.ofPartition_injective n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_bijection_partition
-- given
  (n : ℕ) :
-- imply
  Function.Bijective (fun x : Subtype (fun (p : Nat.Partition n) => Multiset.card p.parts ≤ N) => (equivPartition n x : Subtype (fun (mu : NPartition N) => mu.size = n))) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.bijection_partition n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialExp_eq_monomial
  [CommSemiring R]
-- given
  (a : Fin N → ℕ) :
-- imply
  (monomialExp a : MvPolynomial (Fin N) R) = monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialExp_eq_monomial a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialExp_coeff_self
  [CommSemiring R]
-- given
  (a : Fin N → ℕ) :
-- imply
  coeff (Finsupp.equivFunOnFinite.symm a) (monomialExp a : MvPolynomial (Fin N) R) = 1 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialExp_coeff_self a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialExp_coeff_ne
  [CommSemiring R]
-- given
  (a b : Fin N → ℕ)
  (h : a ≠ b) :
-- imply
  coeff (Finsupp.equivFunOnFinite.symm b) (monomialExp a : MvPolynomial (Fin N) R) = 0 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialExp_coeff_ne a b h

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialExp_totalDegree
  [CommSemiring R]
  [Nontrivial R]
-- given
  (a : Fin N → ℕ) :
-- imply
  (monomialExp a : MvPolynomial (Fin N) R).totalDegree = ∑ i, a i := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialExp_totalDegree a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialExp_zero
  [CommSemiring R] :
-- imply
  (monomialExp (0 : Fin N → ℕ) : MvPolynomial (Fin N) R) = 1 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialExp_zero

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialExp_add
  [CommSemiring R]
-- given
  (a b : Fin N → ℕ) :
-- imply
  (monomialExp (a + b) : MvPolynomial (Fin N) R) = monomialExp a * monomialExp b := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialExp_add a b

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_sorted_length
-- given
  (a : Fin N → ℕ) :
-- imply
  ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_sorted_length a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_parts_eq
-- given
  (a : Fin N → ℕ)
  (i : Fin N) :
-- imply
  (sortTuple a).parts i = ((Finset.univ.val.map a).sort (· ≥ ·)).get ⟨i.val, by simp⟩ := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_parts_eq a i

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_sum_eq
-- given
  (a : Fin N → ℕ) :
-- imply
  ∑ i, (sortTuple a).parts i = ∑ i, a i := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_sum_eq a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_size
-- given
  (a : Fin N → ℕ) :
-- imply
  (sortTuple a).size = ∑ i, a i := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_size a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_of_antitone
-- given
  (a : Fin N → ℕ)
  (ha : Antitone a) :
-- imply
  (sortTuple a).parts = a := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_of_antitone a ha

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_of_NPartition
-- given
  (mu : NPartition N) :
-- imply
  sortTuple mu.parts = mu := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_of_NPartition mu

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_idempotent
-- given
  (a : Fin N → ℕ) :
-- imply
  sortTuple (sortTuple a).parts = sortTuple a := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_idempotent a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_eq_iff
-- given
  (a b : Fin N → ℕ) :
-- imply
  sortTuple a = sortTuple b ↔ (Finset.univ.val.map a) = (Finset.univ.val.map b) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_eq_iff a b

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTuple_comp_perm
-- given
  (a : Fin N → ℕ)
  (σ : Perm (Fin N)) :
-- imply
  sortTuple (a ∘ σ) = sortTuple a := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_comp_perm a σ

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_isSymmetric
  [CommSemiring R]
-- given
  (mu : NPartition N) :
-- imply
  (monomialSymm mu : MvPolynomial (Fin N) R).IsSymmetric := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_isSymmetric mu

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_parts_mem_sortPreimage
-- given
  (mu : NPartition N) :
-- imply
  mu.parts ∈ sortPreimage mu := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.parts_mem_sortPreimage mu

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_coeff_self
  [CommSemiring R]
-- given
  (mu : NPartition N) :
-- imply
  coeff (Finsupp.equivFunOnFinite.symm mu.parts) (monomialSymm mu : MvPolynomial (Fin N) R) = 1 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_coeff_self mu

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_coeff_ne
  [CommSemiring R]
-- given
  (mu nu : NPartition N)
  (h : mu ≠ nu) :
-- imply
  coeff (Finsupp.equivFunOnFinite.symm mu.parts) (monomialSymm nu : MvPolynomial (Fin N) R) = 0 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_coeff_ne mu nu h

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_elem_symm_eq_monomialSymm
  [CommSemiring R]
  [DecidableEq (Fin N)]
-- given
  (n : ℕ)
  (hn : n ≤ N) :
-- imply
  esymm (Fin N) R n = monomialSymm (onesThenZeros n hn) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.elem_symm_eq_monomialSymm n hn

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_mem_NPartitionsOfSize
-- given
  (mu : NPartition N)
  (n : ℕ) :
-- imply
  mu ∈ NPartitionsOfSize n ↔ mu.size = n := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.mem_NPartitionsOfSize mu n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_finite_of_size
-- given
  (n : ℕ) :
-- imply
  Set.Finite { μ : NPartition N | μ.size = n } := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.finite_of_size n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_homog_symm_eq_sum_monomialSymm
  [CommSemiring R]
  [DecidableEq (Fin N)]
-- given
  (n : ℕ) :
-- imply
  hsymm (Fin N) R n = ∑ mu ∈ NPartitionsOfSize n, monomialSymm mu := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.homog_symm_eq_sum_monomialSymm n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_power_sum_eq_monomialSymm
  [CommSemiring R]
  [DecidableEq (Fin N)]
-- given
  (n : ℕ)
  (hn : n ≠ 0)
  (hN : 0 < N) :
-- imply
  psum (Fin N) R n = monomialSymm (singletonPartition n hN) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.power_sum_eq_monomialSymm n hn hN

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_psum_zero_eq_N
  [CommSemiring R] :
-- imply
  psum (Fin N) R 0 = N := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.psum_zero_eq_N

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_zero_partition_eq_one
  [CommSemiring R]
-- given
  (hN : 0 < N) :
-- imply
  monomialSymm (R := R) (singletonPartition 0 hN) = 1 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_zero_partition_eq_one hN

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sigma_coeff_permute
  [CommSemiring R]
-- given
  (sigma : Perm (Fin N))
  (f : MvPolynomial (Fin N) R)
  (a : Fin N → ℕ) :
-- imply
  coeff (Finsupp.equivFunOnFinite.symm a) (rename sigma f) = coeff (Finsupp.equivFunOnFinite.symm (a ∘ sigma)) f := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sigma_coeff_permute sigma f a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_linearIndependent
  [CommSemiring R]
-- given
  (S : Finset (NPartition N)) :
-- imply
  LinearIndependent R (fun mu : S => (monomialSymm mu.val : MvPolynomial (Fin N) R)) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_linearIndependent S

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_coeff_perm_eq_of_symmetric
  [CommSemiring R]
-- given
  (f : MvPolynomial (Fin N) R)
  (hf : f.IsSymmetric)
  (d : Finsupp (Fin N) ℕ)
  (σ : Perm (Fin N)) :
-- imply
  coeff (Finsupp.mapDomain σ d) f = coeff d f := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.coeff_perm_eq_of_symmetric f hf d σ

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_support_closed_under_perm
  [CommSemiring R]
-- given
  (f : MvPolynomial (Fin N) R)
  (d : Finsupp (Fin N) ℕ)
  (hf : f.IsSymmetric)
  (hd : d ∈ f.support)
  (σ : Perm (Fin N)) :
-- imply
  Finsupp.mapDomain σ d ∈ f.support := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.support_closed_under_perm f hf d hd σ

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_sortTupleFinsupp_perm
-- given
  (d : Finsupp (Fin N) ℕ)
  (σ : Perm (Fin N)) :
-- imply
  sortTupleFinsupp (Finsupp.mapDomain σ d) = sortTupleFinsupp d := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTupleFinsupp_perm d σ

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_coeff_eq_of_same_sort
  [CommSemiring R]
-- given
  (f : MvPolynomial (Fin N) R)
  (d₁ d₂ : Finsupp (Fin N) ℕ)
  (hf : f.IsSymmetric)
  (h : sortTupleFinsupp d₁ = sortTupleFinsupp d₂) :
-- imply
  coeff d₁ f = coeff d₂ f := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.coeff_eq_of_same_sort f hf d₁ d₂ h

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_spans
  [CommSemiring R] :
-- imply
  ∀ f : MvPolynomial (Fin N) R, f.IsSymmetric → f ∈ Submodule.span R (Set.range (fun mu : NPartition N => monomialSymm mu)) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_spans

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_symm_eq_sum_coeff_monomialSymm
  [CommSemiring R]
-- given
  (f : MvPolynomial (Fin N) R)
  (S : Finset (NPartition N))
  (hf : f.IsSymmetric)
  (hS : ∀ mu : NPartition N, mu.size ≤ f.totalDegree → mu ∈ S) :
-- imply
  f = ∑ mu ∈ S, (coeff (Finsupp.equivFunOnFinite.symm mu.parts) f) • monomialSymm mu := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.symm_eq_sum_coeff_monomialSymm f hf S hS

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_isHomogeneous
  [CommSemiring R]
-- given
  (mu : NPartition N) :
-- imply
  (monomialSymm mu : MvPolynomial (Fin N) R).IsHomogeneous mu.size := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_isHomogeneous mu

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_homogeneous_spans
  [CommSemiring R]
-- given
  (n : ℕ) :
-- imply
  ∀ f ∈ symmHomogeneous N R n, f ∈ Submodule.span R (Set.range (fun mu : Subtype (fun (nu : NPartition N) => nu.size = n) => monomialSymm mu.val)) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_homogeneous_spans n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma ms_monomialSymm_homogeneous_linearIndependent
  [CommSemiring R]
-- given
  (n : ℕ) :
-- imply
  LinearIndependent R (fun mu : Subtype (fun (nu : NPartition N) => nu.size = n) => (monomialSymm mu.val : MvPolynomial (Fin N) R)) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_homogeneous_linearIndependent n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_finset_card_filter_get_eq_count
  [DecidableEq α]
-- given
  (L : List α)
  (x : α) :
-- imply
  (Finset.filter (fun i : Fin L.length => L.get i = x) Finset.univ).card = L.count x := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.finset_card_filter_get_eq_count L x

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_toPartition_ofPartition_parts
  {N n : ℕ}
-- given
  (p : Nat.Partition n)
  (hp : Multiset.card p.parts ≤ N) :
-- imply
  (ofPartition p hp).toPartition.parts = p.parts := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.toPartition_ofPartition_parts p hp

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_antitone_zero_tail
  {N : ℕ}
-- given
  (f : Fin N → ℕ)
  (i j : Fin N)
  (hf : Antitone f)
  (hi : f i = 0)
  (hij : i ≤ j) :
-- imply
  f j = 0 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.antitone_zero_tail f hf i j hi hij

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_lt_filter_length_iff_ne_zero
  {N : ℕ}
-- given
  (f : Fin N → ℕ)
  (hf : Antitone f)
  (i : Fin N) :
-- imply
  i.val < ((List.ofFn f).filter (· ≠ 0)).length ↔ f i ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.lt_filter_length_iff_ne_zero f hf i

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_list_ofFn_pairwise_of_antitone
  {N : ℕ}
-- given
  (f : Fin N → ℕ)
  (hf : Antitone f) :
-- imply
  (List.ofFn f).Pairwise (· ≥ ·) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.list_ofFn_pairwise_of_antitone f hf

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_filter_nonzero_pairwise_of_antitone
  {N : ℕ}
-- given
  (f : Fin N → ℕ)
  (hf : Antitone f) :
-- imply
  ((List.ofFn f).filter (· ≠ 0)).Pairwise (· ≥ ·) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.filter_nonzero_pairwise_of_antitone f hf

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_sort_filter_nonzero_eq_self
  {N : ℕ}
-- given
  (f : Fin N → ℕ)
  (hf : Antitone f) :
-- imply
  (↑((List.ofFn f).filter (· ≠ 0)) : Multiset ℕ).sort (· ≥ ·) = (List.ofFn f).filter (· ≠ 0) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.sort_filter_nonzero_eq_self f hf

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_finset_univ_val_map_eq_ofFn
  {N : ℕ}
-- given
  (f : Fin N → ℕ) :
-- imply
  (Finset.univ.val.map f : Multiset ℕ) = ↑(List.ofFn f) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.finset_univ_val_map_eq_ofFn f

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_filter_nonzero_eq_take
  {N : ℕ}
-- given
  (f : Fin N → ℕ)
  (hf : Antitone f) :
-- imply
  (List.ofFn f).filter (· ≠ 0) = (List.ofFn f).take ((List.ofFn f).filter (· ≠ 0)).length := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.NPartition.filter_nonzero_eq_take f hf

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_map_comp_perm_eq
  {N : ℕ}
-- given
  (a : Fin N → ℕ)
  (σ : Perm (Fin N)) :
-- imply
  (Finset.univ.val.map (a ∘ σ)) = (Finset.univ.val.map a) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.map_comp_perm_eq a σ

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_rename_monomialExp
  [CommSemiring R]
  {N : ℕ}
-- given
  (σ : Perm (Fin N))
  (a : Fin N → ℕ) :
-- imply
  rename σ (monomialExp (R := R) a) = monomialExp (a ∘ σ.symm) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.rename_monomialExp σ a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_mem_sortPreimage_comp_perm
  {N : ℕ}
  {a : Fin N → ℕ}
  {mu : NPartition N}
-- given
  (ha : a ∈ sortPreimage mu)
  (σ : Perm (Fin N)) :
-- imply
  (a ∘ σ.symm) ∈ sortPreimage mu := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.mem_sortPreimage_comp_perm σ ha

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_mem_sortPreimage_comp_perm'
  {N : ℕ}
  {a : Fin N → ℕ}
  {mu : NPartition N}
-- given
  (ha : a ∈ sortPreimage mu)
  (σ : Perm (Fin N)) :
-- imply
  (a ∘ σ) ∈ sortPreimage mu := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.mem_sortPreimage_comp_perm' σ ha

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_prod_subset_eq_prod_indicator
  [CommSemiring R]
  {N : ℕ}
-- given
  (S : Finset (Fin N)) :
-- imply
  (∏ i ∈ S, X i : MvPolynomial (Fin N) R) = ∏ j : Fin N, X j ^ (if j ∈ S then 1 else 0) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.prod_subset_eq_prod_indicator S

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_X_pow_eq_prod_single
  [CommSemiring R]
  {N : ℕ}
-- given
  (i : Fin N)
  (n : ℕ) :
-- imply
  (X i : MvPolynomial (Fin N) R) ^ n = ∏ j : Fin N, X j ^ (if j = i then n else 0) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.X_pow_eq_prod_single i n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_multiset_prod_map_X_eq_prod_pow
  [CommSemiring R]
  {N : ℕ}
-- given
  (s : Multiset (Fin N)) :
-- imply
  (s.map (X : Fin N → MvPolynomial (Fin N) R)).prod = ∏ i : Fin N, X i ^ (Multiset.count i s) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.multiset_prod_map_X_eq_prod_pow s

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_sortTuple_indicatorTuple
  {N n : ℕ}
-- given
  (S : Finset (Fin N))
  (hn : S.card = n)
  (hn' : n ≤ N) :
-- imply
  sortTuple (indicatorTuple S) = onesThenZeros n hn' := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_indicatorTuple S hn hn'

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_sortTuple_singleTuple
  {N : ℕ}
-- given
  (hN : 0 < N)
  (i : Fin N)
  (n : ℕ) :
-- imply
  sortTuple (singleTuple i n) = singletonPartition n hN := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_singleTuple i n hN

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_sortTuple_countTuple_size
  {N n : ℕ}
-- given
  (s : Sym (Fin N) n) :
-- imply
  (sortTuple (countTuple s)).size = n := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_countTuple_size s

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_indicatorTuple_mem_sortPreimage
  {N n : ℕ}
-- given
  (S : Finset (Fin N))
  (hn : S.card = n)
  (hn' : n ≤ N) :
-- imply
  indicatorTuple S ∈ sortPreimage (onesThenZeros n hn') := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.indicatorTuple_mem_sortPreimage S hn hn'

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_singleTuple_mem_sortPreimage
  {N : ℕ}
-- given
  (hN : 0 < N)
  (i : Fin N)
  (n : ℕ) :
-- imply
  singleTuple i n ∈ sortPreimage (singletonPartition n hN) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.singleTuple_mem_sortPreimage i n hN

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_monomialExp_singleTuple
  [CommSemiring R]
  {N : ℕ}
-- given
  (i : Fin N)
  (n : ℕ) :
-- imply
  (monomialExp (singleTuple i n) : MvPolynomial (Fin N) R) = X i ^ n := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialExp_singleTuple i n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_sortPreimage_singletonPartition_values
  {N : ℕ}
-- given
  (a : Fin N → ℕ)
  (n : ℕ)
  (hN : 0 < N)
  (ha : a ∈ sortPreimage (singletonPartition n hN))
  (i : Fin N) :
-- imply
  a i = 0 ∨ a i = n := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortPreimage_singletonPartition_values a n hN ha i

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_mem_sortPreimage_singletonPartition_exists_singleTuple
  {N : ℕ}
-- given
  (a : Fin N → ℕ)
  (n : ℕ)
  (hn : n ≠ 0)
  (hN : 0 < N)
  (ha : a ∈ sortPreimage (singletonPartition n hN)) :
-- imply
  ∃ i, a = singleTuple i n := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.mem_sortPreimage_singletonPartition_exists_singleTuple a n hn hN ha

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_indicatorSupport_indicatorTuple
  {N : ℕ}
-- given
  (S : Finset (Fin N)) :
-- imply
  indicatorSupport (indicatorTuple S) = S := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.indicatorSupport_indicatorTuple S

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_sortPreimage_onesThenZeros_values
  {N n : ℕ}
-- given
  (a : Fin N → ℕ)
  (hn' : n ≤ N)
  (ha : a ∈ sortPreimage (onesThenZeros n hn'))
  (i : Fin N) :
-- imply
  a i = 0 ∨ a i = 1 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortPreimage_onesThenZeros_values a hn' ha i

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_indicatorTuple_indicatorSupport
  {N n : ℕ}
-- given
  (a : Fin N → ℕ)
  (hn' : n ≤ N)
  (ha : a ∈ sortPreimage (onesThenZeros n hn')) :
-- imply
  indicatorTuple (indicatorSupport a) = a := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.indicatorTuple_indicatorSupport a hn' ha

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_indicatorSupport_card
  {N n : ℕ}
-- given
  (a : Fin N → ℕ)
  (hn' : n ≤ N)
  (ha : a ∈ sortPreimage (onesThenZeros n hn')) :
-- imply
  (indicatorSupport a).card = n := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.indicatorSupport_card a hn' ha

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_prod_subset_eq_monomialExp
  [CommSemiring R]
  {N : ℕ}
-- given
  (S : Finset (Fin N)) :
-- imply
  (∏ i ∈ S, X i : MvPolynomial (Fin N) R) = monomialExp (indicatorTuple S) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.prod_subset_eq_monomialExp S

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_sum_partition
  [DecidableEq α]
  [DecidableEq β]
  [AddCommMonoid M]
-- given
  (s : Finset α)
  (f : α → β)
  (g : α → M) :
-- imply
  ∑ x ∈ s, g x = ∑ y ∈ s.image f, ∑ x ∈ s.filter (fun x => f x = y), g x := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sum_partition s f g

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_fiber_equiv_val_eq
  [DecidableEq α]
  [DecidableEq β]
  [Fintype α]
-- given
  (a b : α → β)
  (v w : β)
  (j : α)
  (hcount : ∀ v, (Finset.univ.filter (fun i => a i = v)).card = (Finset.univ.filter (fun i => b i = v)).card)
  (hvw : v = w)
  (hj_v : j ∈ Finset.univ.filter (fun k => b k = v))
  (hj_w : j ∈ Finset.univ.filter (fun k => b k = w)) :
-- imply
  ((Finset.equivOfCardEq (hcount v)).symm ⟨j, hj_v⟩).val = ((Finset.equivOfCardEq (hcount w)).symm ⟨j, hj_w⟩).val := by
-- proof
  subst hvw
  rfl

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_exists_perm_of_map_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
-- given
  (a b : α → β)
  (h : Finset.univ.val.map a = Finset.univ.val.map b) :
-- imply
  ∃ σ : Perm α, ∀ i, b i = a (σ i) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.exists_perm_of_map_eq a b h

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_sortTuple_eq_implies_multiset_eq
  {N : ℕ}
-- given
  (a b : Fin N → ℕ)
  (h : sortTuple a = sortTuple b) :
-- imply
  (Finset.univ.val.map a) = (Finset.univ.val.map b) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.sortTuple_eq_implies_multiset_eq a b h

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_monomialExp_isHomogeneous
  [CommSemiring R]
  {N : ℕ}
-- given
  (a : Fin N → ℕ) :
-- imply
  (monomialExp a : MvPolynomial (Fin N) R).IsHomogeneous (∑ i, a i) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialExp_isHomogeneous a

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_homogeneousComponent_monomialSymm
  [CommSemiring R]
  {N : ℕ}
-- given
  (mu : NPartition N)
  (n : ℕ) :
-- imply
  homogeneousComponent n (monomialSymm (R := R) mu) = if mu.size = n then monomialSymm mu else 0 := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.homogeneousComponent_monomialSymm mu n

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_linearIndependent_submodule_of_linearIndependent
  [CommSemiring R]
  {N : ℕ}
  {S : Submodule R (MvPolynomial (Fin N) R)}
-- given
  (v : ι → S)
  (hli : LinearIndependent R (fun i => (v i : MvPolynomial (Fin N) R))) :
-- imply
  LinearIndependent R v := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.linearIndependent_submodule_of_linearIndependent v hli

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_span_eq_top_of_subtype_span
  [CommSemiring R]
  {ι : Type*}
  {N : ℕ}
  {S : Submodule R (MvPolynomial (Fin N) R)}
-- given
  (v : ι → S)
  (hsp : ∀ x : S, (x : MvPolynomial (Fin N) R) ∈ Submodule.span R (Set.range (fun i => (v i : MvPolynomial (Fin N) R)))) :
-- imply
  ⊤ ≤ Submodule.span R (Set.range v) := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.span_eq_top_of_subtype_span v hsp

/--
[MonomialSymmetric](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SymmetricFunctions/MonomialSymmetric.lean)
-/
@[path]
private lemma pv_monomialSymm_mem_symmHomogeneous'
  [CommSemiring R]
  {N : ℕ}
-- given
  (mu : NPartition N)
  (n : ℕ)
  (h : mu.size = n) :
-- imply
  (monomialSymm mu : MvPolynomial (Fin N) R) ∈ symmHomogeneous N R n := by
-- proof
  apply AlgebraicCombinatorics.SymmetricFunctions.monomialSymm_mem_symmHomogeneous' mu n h


-- created on 2026-10-23
