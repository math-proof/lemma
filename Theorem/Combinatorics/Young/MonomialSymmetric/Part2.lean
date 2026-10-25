/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Abbrev.Combinatorics.Young.MonomialSymmetric.Part2
open scoped Polynomial
open MvPolynomial Finset Equiv

/-!
# N-partitions and Monomial Symmetric Polynomials

This file formalizes N-partitions and monomial symmetric polynomials,
following Section sec.sf.m of the source.

## Main definitions

* `NPartition N` - a weakly decreasing N-tuple of nonnegative integers
  (Definition def.sf.Npar) — alias for canonical definition in `NPartition.lean`
* `NPartition.size` - the sum of entries of an N-partition (|λ|)
* `NPartition.ofPartition` - converts a partition of length ≤ N to an N-partition
  by padding with zeros (Proposition prop.sf.Npar-as-par) — re-exported from `NPartition.lean`
* `NPartition.toPartition` - converts an N-partition to a partition by removing zeros
  — re-exported from `NPartition.lean`
* `NPartition.equivPartition` - the equivalence (bijection) between partitions of
  length ≤ N and N-partitions (Proposition prop.sf.Npar-as-par)
* `monomialExp` - x^a for a ∈ ℕ^N (Definition def.sf.sort (a))
* `sortTuple` - sorts a tuple in weakly decreasing order (Definition def.sf.sort (b))
* `monomialSymm` - the monomial symmetric polynomial m_λ (Definition def.sf.m)
* `symmHomogeneous` - the submodule of homogeneous symmetric polynomials of degree n
  (Theorem thm.sf.m-basis (c))

## Main results

* `NPartition.bijection_partition` - bijection between partitions of length ≤ N and N-partitions
  (Proposition prop.sf.Npar-as-par)
* `elem_symm_eq_monomialSymm` - e_n expressed via monomial symmetric polynomials
  (Proposition prop.sf.ehp-through-m (a))
* `homog_symm_eq_sum_monomialSymm` - h_n as sum of m_μ over |μ| = n
  (Proposition prop.sf.ehp-through-m (b))
* `power_sum_eq_monomialSymm` - p_n expressed via monomial symmetric polynomials
  (Proposition prop.sf.ehp-through-m (c))
* `monomialSymm_linearIndependent` - the family (m_μ) is linearly independent
  (Theorem thm.sf.m-basis (a), part 1)
* `monomialSymm_spans` - the family (m_μ) spans the symmetric polynomials
  (Theorem thm.sf.m-basis (a), part 2)
* `symm_eq_sum_coeff_monomialSymm` - expansion formula for symmetric polynomials
  (Theorem thm.sf.m-basis (b))
* `monomialSymm_homogeneous_linearIndependent` - the family (m_μ) with |μ| = n is linearly independent
  (Theorem thm.sf.m-basis (d), linear independence)
* `monomialSymm_homogeneous_spans` - the family (m_μ) with |μ| = n spans 𝒮_n
  (Theorem thm.sf.m-basis (d), spanning)
* `monomialSymm_basis_homogeneous` - the family (m_μ) with |μ| = n forms a basis of 𝒮_n
  (Theorem thm.sf.m-basis (d))
* `sigma_coeff_permute` - permutation transforms polynomial coefficients
  (Proposition prop.sf.sigma-pol-coeff)

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/MonomialSymmetric.tex

## Implementation notes

We use `Fin N → ℕ` to represent N-tuples of nonnegative integers.
The ordering on `Fin N` is the standard one, and "weakly decreasing" means
`∀ i j, i ≤ j → μ j ≤ μ i` (i.e., antitone with respect to the standard order on Fin N).

Mathlib already has `MvPolynomial.msymm` for monomial symmetric polynomials indexed by
`Nat.Partition`. Our `NPartition` provides an alternative indexing that is more natural
for the N-variable setting and corresponds directly to the textbook presentation.
-/


/-! Compatibility with the pre-2026 `MvPolynomial.coeff m p` argument order.
`MvPolynomial.coeff` is now the coefficient `Finsupp`, so `p.coeff m` is the new spelling.
These declarations restore `coeff m p` and the lemmas the proofs rewrite with. -/


namespace AlgebraicCombinatorics

namespace SymmetricFunctions

variable {R : Type*} [CommSemiring R]

variable {N : ℕ}

variable {σ : Type*}

namespace NPartition

/-- The size of ofPartition p equals n (the sum of the original partition).
    Re-export of `_root_.NPartition.ofPartition_size`. -/
theorem ofPartition_size {n : ℕ} (p : Nat.Partition n) (hp : Multiset.card p.parts ≤ N) :
    (ofPartition p hp).size = n :=
  _root_.NPartition.ofPartition_size p hp

/-- The number of non-zero parts of an N-partition is at most N.
    Re-export of `_root_.NPartition.toPartition_card_le`. -/
theorem toPartition_card_le (mu : NPartition N) :
    Multiset.card mu.toPartition.parts ≤ N :=
  _root_.NPartition.toPartition_card_le mu

/-- Helper lemma: #{i : Fin n | L[i] = x} = List.count x L -/
theorem finset_card_filter_get_eq_count {α : Type*} [DecidableEq α] (L : List α) (x : α) :
    (Finset.filter (fun i : Fin L.length => L.get i = x) Finset.univ).card = L.count x := by
  induction L with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons, List.count_cons]
    have key : (Finset.filter (fun i : Fin (as.length + 1) => (a :: as).get i = x) Finset.univ).card =
               (if a = x then 1 else 0) + (Finset.filter (fun i : Fin as.length => as.get i = x) Finset.univ).card := by
      let S₀ : Finset (Fin (as.length + 1)) := if a = x then {0} else ∅
      let S₁ : Finset (Fin (as.length + 1)) := (Finset.filter (fun i : Fin as.length => as.get i = x) Finset.univ).map
                                                ⟨Fin.succ, Fin.succ_injective _⟩
      have hS₀_card : S₀.card = if a = x then 1 else 0 := by simp only [S₀]; split_ifs <;> simp
      have hS₁_card : S₁.card = (Finset.filter (fun i : Fin as.length => as.get i = x) Finset.univ).card := by
        simp only [S₁, Finset.card_map]
      have hdisj : Disjoint S₀ S₁ := by
        simp only [S₀, S₁]; rw [Finset.disjoint_left]; intro i hi
        split_ifs at hi with ha
        · simp only [Finset.mem_singleton] at hi
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                     Function.Embedding.coeFn_mk, not_exists, not_and]
          intro j _; rw [hi]; intro heq; exact Fin.succ_ne_zero j heq
        · simp at hi
      have hunion : Finset.filter (fun i : Fin (as.length + 1) => (a :: as).get i = x) Finset.univ = S₀ ∪ S₁ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, S₀, S₁]
        constructor
        · intro hi; cases' i using Fin.cases with j
          · left; simp only [List.get_cons_zero] at hi; rw [if_pos hi]; exact Finset.mem_singleton_self 0
          · right; simp only [List.get_eq_getElem] at hi
            simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
            exact ⟨j, hi, rfl⟩
        · intro hi; rcases hi with (hi | hi)
          · split_ifs at hi with ha
            · simp only [Finset.mem_singleton] at hi; subst hi; simp [ha]
            · simp at hi
          · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hi
            obtain ⟨j, hj, rfl⟩ := hi; simp only [List.get_eq_getElem]; exact hj
      rw [hunion, Finset.card_union_of_disjoint hdisj, hS₀_card, hS₁_card]
    rw [key, ih]
    by_cases ha : a = x
    · simp only [ha, ↓reduceIte, beq_self_eq_true]; ring
    · simp only [ha, ↓reduceIte, beq_false_of_ne ha, Bool.false_eq_true]; ring

/-- Key lemma for left_inv: toPartition (ofPartition p hp).parts = p.parts -/
theorem toPartition_ofPartition_parts {n : ℕ} (p : Nat.Partition n) (hp : Multiset.card p.parts ≤ N) :
    (ofPartition p hp).toPartition.parts = p.parts := by
  simp only [_root_.NPartition.toPartition, _root_.NPartition.ofPartition]

  set sorted := p.parts.sort (· ≥ ·) with hsorted_def
  set f : Fin N → ℕ := fun i => if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0 with hf_def

  have hlen : sorted.length = Multiset.card p.parts := Multiset.length_sort (· ≥ ·)
  have hsorted_le : sorted.length ≤ N := hlen ▸ hp
  have hsorted_eq : (sorted : Multiset ℕ) = p.parts := by simp [sorted]

  -- All elements of sorted are positive
  have hsorted_pos : ∀ x ∈ sorted, 0 < x := by
    intro x hx
    have : x ∈ p.parts := by rw [← hsorted_eq]; exact Multiset.mem_coe.mpr hx
    exact p.parts_pos this

  -- Prove by multiset extensionality
  ext x
  simp only [Multiset.count_filter, Multiset.count_map]

  by_cases hx : x = 0
  · -- x = 0: both sides are 0
    subst hx
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    symm
    rw [Multiset.count_eq_zero]
    exact fun h => Nat.lt_irrefl 0 (p.parts_pos h)
  · -- x ≠ 0
    rw [if_pos hx, ← hsorted_eq, Multiset.coe_count]

    have hfilter_card : (Finset.filter (fun a : Fin N => x = f a) Finset.univ).card =
                        List.count x sorted := by
      have h_f_val : ∀ i : Fin N, x = f i ↔ ∃ h : i.val < sorted.length, sorted.get ⟨i.val, h⟩ = x := by
        intro i; simp only [f]
        constructor
        · intro heq
          by_cases hlt : i.val < sorted.length
          · exact ⟨hlt, by simp only [hlt, ↓reduceDIte] at heq; exact heq.symm⟩
          · simp only [hlt, ↓reduceDIte] at heq; exact absurd heq hx
        · intro ⟨hlt, hget⟩; simp only [hlt, ↓reduceDIte, hget]

      have hcard_eq : (Finset.filter (fun a : Fin N => x = f a) Finset.univ).card =
                      (Finset.filter (fun a : Fin sorted.length => sorted.get a = x) Finset.univ).card := by
        refine Finset.card_bij (fun i hi => ⟨i.val, ?_⟩) ?_ ?_ ?_
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          obtain ⟨hlt, _⟩ := (h_f_val i).mp hi; exact hlt
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          obtain ⟨hlt, hget⟩ := (h_f_val i).mp hi; exact hget
        · intro i j _ _ heq; simp only [Fin.mk.injEq] at heq; exact Fin.ext heq
        · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hjN : j.val < N := Nat.lt_of_lt_of_le j.isLt hsorted_le
          refine ⟨⟨j.val, hjN⟩, ?_, by simp⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (h_f_val ⟨j.val, hjN⟩).mpr ⟨j.isLt, hj⟩

      rw [hcard_eq, finset_card_filter_get_eq_count]

    exact hfilter_card

/-- Helper lemma: casting a partition preserves its parts. -/
theorem Nat.Partition.parts_cast {m n : ℕ} (h : m = n) (p : Nat.Partition m) :
    (h ▸ p).parts = p.parts := by
  induction h
  rfl

/-- For an antitone function, if f i = 0 and j ≥ i, then f j = 0.
    (Helper for right_inv of equivPartition) -/
theorem antitone_zero_tail (f : Fin N → ℕ) (hf : Antitone f) (i j : Fin N)
    (hi : f i = 0) (hij : i ≤ j) : f j = 0 := by
  have : f j ≤ f i := hf hij
  omega

/-- For an antitone function f : Fin N → ℕ, the position i is less than the length of
    the filtered list (filter (· ≠ 0)) if and only if f i ≠ 0.
    (Helper for right_inv of equivPartition) -/
theorem lt_filter_length_iff_ne_zero (f : Fin N → ℕ) (hf : Antitone f) (i : Fin N) :
    i.val < ((List.ofFn f).filter (· ≠ 0)).length ↔ f i ≠ 0 := by
  constructor
  · intro hi hfi
    have hbound : ∀ j : Fin N, f j ≠ 0 → j.val < i.val := fun j hfj => by
      by_contra hge
      push Not at hge
      exact hfj (antitone_zero_tail f hf i j hfi (Fin.mk_le_mk.mpr hge))
    have hlen_le : ((List.ofFn f).filter (· ≠ 0)).length ≤ i.val := by
      rw [List.countP_eq_length_filter.symm]
      have hsplit : List.ofFn f = (List.ofFn f).take i.val ++ (List.ofFn f).drop i.val :=
        (List.take_append_drop i.val (List.ofFn f)).symm
      rw [hsplit, List.countP_append]
      have hdrop_zero : ((List.ofFn f).drop i.val).countP (· ≠ 0) = 0 := by
        apply List.countP_eq_zero.mpr
        intro x hx
        rw [List.mem_drop_iff_getElem] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        simp only [decide_eq_true_eq, not_not, List.getElem_ofFn, List.length_ofFn] at hj ⊢
        exact antitone_zero_tail f hf i ⟨i.val + j, by omega⟩ hfi (Fin.mk_le_mk.mpr (by omega))
      rw [hdrop_zero, add_zero]
      calc ((List.ofFn f).take i.val).countP (· ≠ 0)
          ≤ ((List.ofFn f).take i.val).length := List.countP_le_length
        _ = min i.val N := by simp [List.length_take, List.length_ofFn]
        _ ≤ i.val := min_le_left _ _
    omega
  · intro hfi
    have h_prefix_nonzero : ∀ j : Fin N, j ≤ i → f j ≠ 0 := fun j hji hfj =>
      hfi (antitone_zero_tail f hf j i hfj hji)
    have hiN : i.val + 1 ≤ N := Nat.succ_le_of_lt i.isLt
    have hlen_ge : i.val + 1 ≤ ((List.ofFn f).filter (· ≠ 0)).length := by
      rw [List.countP_eq_length_filter.symm]
      have hsplit : List.ofFn f = (List.ofFn f).take (i.val + 1) ++ (List.ofFn f).drop (i.val + 1) := by
        simp [List.take_append_drop]
      rw [hsplit, List.countP_append]
      have htake_countP : ((List.ofFn f).take (i.val + 1)).countP (· ≠ 0) = i.val + 1 := by
        rw [List.countP_eq_length_filter]
        have hfilter_eq : ((List.ofFn f).take (i.val + 1)).filter (· ≠ 0) =
                          (List.ofFn f).take (i.val + 1) := by
          apply List.filter_eq_self.mpr
          intro x hx
          rw [List.mem_take_iff_getElem] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          simp only [decide_eq_true_eq, List.getElem_ofFn, List.length_ofFn] at hj ⊢
          exact h_prefix_nonzero ⟨j, by omega⟩ (Fin.mk_le_mk.mpr (by omega))
        rw [hfilter_eq]
        simp only [List.length_take, List.length_ofFn, min_eq_left hiN]
      omega
    omega

/-- For an antitone function f : Fin N → ℕ, List.ofFn f is pairwise ≥ (sorted descending).
    (Helper for right_inv of equivPartition) -/
theorem list_ofFn_pairwise_of_antitone (f : Fin N → ℕ) (hf : Antitone f) :
    (List.ofFn f).Pairwise (· ≥ ·) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  simp only [List.get_ofFn]
  exact hf (Fin.mk_le_mk.mpr (le_of_lt hij))

/-- For an antitone function, filtering zeros preserves the pairwise ≥ property.
    (Helper for right_inv of equivPartition) -/
theorem filter_nonzero_pairwise_of_antitone (f : Fin N → ℕ) (hf : Antitone f) :
    ((List.ofFn f).filter (· ≠ 0)).Pairwise (· ≥ ·) :=
  List.Pairwise.filter (· ≠ 0) (list_ofFn_pairwise_of_antitone f hf)

/-- For an antitone function, sorting the filtered list gives the same list.
    (Helper for right_inv of equivPartition) -/
theorem sort_filter_nonzero_eq_self (f : Fin N → ℕ) (hf : Antitone f) :
    (↑((List.ofFn f).filter (· ≠ 0)) : Multiset ℕ).sort (· ≥ ·) =
    (List.ofFn f).filter (· ≠ 0) := by
  simp only [Multiset.coe_sort]
  exact List.mergeSort_eq_self (r := (· ≥ ·)) (filter_nonzero_pairwise_of_antitone f hf)

/-- Finset.univ.val.map f equals the multiset coercion of List.ofFn f.
    (Helper for right_inv of equivPartition) -/
theorem finset_univ_val_map_eq_ofFn (f : Fin N → ℕ) :
    (Finset.univ.val.map f : Multiset ℕ) = ↑(List.ofFn f) := by
  change (↑(List.map f (List.finRange N)) : Multiset ℕ) = ↑(List.ofFn f)
  rw [List.ofFn_eq_map]

/-- For an antitone function, filtering out zeros gives a prefix of the original list.
    (Helper for right_inv of equivPartition) -/
theorem filter_nonzero_eq_take (f : Fin N → ℕ) (hf : Antitone f) :
    (List.ofFn f).filter (· ≠ 0) = (List.ofFn f).take ((List.ofFn f).filter (· ≠ 0)).length := by
  set k := ((List.ofFn f).filter (· ≠ 0)).length with hk_def
  have hlen : (List.ofFn f).length = N := List.length_ofFn
  have hk_le : k ≤ N := by
    calc k = ((List.ofFn f).filter (· ≠ 0)).length := rfl
      _ ≤ (List.ofFn f).length := List.length_filter_le _ _
      _ = N := hlen
  -- The filter = take k because:
  -- 1. All elements in positions 0..k-1 are nonzero (so they pass the filter)
  -- 2. All elements in positions k..N-1 are zero (so they don't pass the filter)
  have h_take_all_ne : ∀ x ∈ (List.ofFn f).take k, x ≠ 0 := by
    intro x hx
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    simp only [hlen, List.getElem_ofFn] at hm ⊢
    have hm_lt_k : m < k := by omega
    have hm_lt_N : m < N := by omega
    exact (lt_filter_length_iff_ne_zero f hf ⟨m, hm_lt_N⟩).mp hm_lt_k
  have h_drop_all_zero : ∀ x ∈ (List.ofFn f).drop k, x = 0 := by
    intro x hx
    rw [List.mem_drop_iff_getElem] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    simp only [hlen, List.getElem_ofFn] at hm ⊢
    have hkm_lt_N : k + m < N := by omega
    have h_not_lt : ¬ (k + m < k) := by omega
    by_contra hne
    have : (k + m) < k := (lt_filter_length_iff_ne_zero f hf ⟨k + m, hkm_lt_N⟩).mpr hne
    omega
  have h_take_filter_eq : ((List.ofFn f).take k).filter (· ≠ 0) = (List.ofFn f).take k := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact h_take_all_ne x hx
  have h_drop_filter_empty : ((List.ofFn f).drop k).filter (· ≠ 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp only [decide_eq_true_eq, not_not]
    exact h_drop_all_zero x hx
  calc (List.ofFn f).filter (· ≠ 0)
      = ((List.ofFn f).take k).filter (· ≠ 0) ++ ((List.ofFn f).drop k).filter (· ≠ 0) := by
        rw [← List.filter_append, List.take_append_drop]
    _ = (List.ofFn f).take k ++ [] := by rw [h_take_filter_eq, h_drop_filter_empty]
    _ = (List.ofFn f).take k := List.append_nil _


end NPartition
end SymmetricFunctions
end AlgebraicCombinatorics
