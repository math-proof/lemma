/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.MonomialSymmetric
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

/-!
### API for monomialExp (Definition def.sf.sort (a))
-/


/-- `monomialExp` equals the Mathlib monomial with the given exponent. -/
theorem monomialExp_eq_monomial (a : Fin N → ℕ) :
    (monomialExp a : MvPolynomial (Fin N) R) = monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  simp only [monomialExp, monomial_eq, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Finsupp.equivFunOnFinite_symm_apply_apply]

/-!
### API for sortTuple (Definition def.sf.sort (b))
-/


/-- The length of the sorted list equals N. -/
theorem sortTuple_sorted_length (a : Fin N → ℕ) :
    ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := by
  rw [Multiset.length_sort, Multiset.card_map]
  simp [Finset.card_univ]

/-- Access to the sorted list entries for valid indices. -/
theorem sortTuple_parts_eq (a : Fin N → ℕ) (i : Fin N) :
    (sortTuple a).parts i = ((Finset.univ.val.map a).sort (· ≥ ·)).get ⟨i.val, by
      rw [sortTuple_sorted_length]; exact i.isLt⟩ := by
  simp only [sortTuple]
  split_ifs with h
  · rfl
  · exfalso
    rw [sortTuple_sorted_length] at h
    exact h i.isLt

/-- The sum of entries is preserved by sorting. -/
theorem sortTuple_sum_eq (a : Fin N → ℕ) :
    ∑ i, (sortTuple a).parts i = ∑ i, a i := by
  -- Use the fact that the sorted list as multiset equals original multiset
  have hsort : ↑((Finset.univ.val.map a).sort (· ≥ ·)) = Finset.univ.val.map a :=
    Multiset.sort_eq (r := (· ≥ ·)) (Finset.univ.val.map a)
  have hlen : ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := sortTuple_sorted_length a
  -- Sum over sortTuple equals sum of sorted list
  have h1 : ∑ i, (sortTuple a).parts i =
      ((Finset.univ.val.map a).sort (· ≥ ·)).sum := by
    trans (List.ofFn (sortTuple a).parts).sum
    · rw [List.sum_ofFn]
    · congr 1
      apply List.ext_get
      · simp only [List.length_ofFn]
        rw [hlen]
      · intro i hi1 hi2
        simp only [List.length_ofFn] at hi1
        simp only [List.get_ofFn]
        rw [sortTuple_parts_eq]
        congr 1
  rw [h1]
  -- Sum of sorted list equals sum of original multiset
  have h2 : ((Finset.univ.val.map a).sort (· ≥ ·)).sum = (Finset.univ.val.map a).sum := by
    rw [← Multiset.sum_coe, hsort]
  rw [h2]
  simp [Finset.sum_eq_multiset_sum]

/-- The size of sortTuple a equals the sum of entries of a. -/
theorem sortTuple_size (a : Fin N → ℕ) : (sortTuple a).size = ∑ i, a i :=
  sortTuple_sum_eq a

/-- If a tuple is already antitone (weakly decreasing), sorting doesn't change it. -/
theorem sortTuple_of_antitone (a : Fin N → ℕ) (ha : Antitone a) :
    (sortTuple a).parts = a := by
  ext i
  simp only [sortTuple]
  have hlen : ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := sortTuple_sorted_length a
  have hi_lt : i.val < ((Finset.univ.val.map a).sort (· ≥ ·)).length := by rw [hlen]; exact i.isLt
  rw [dif_pos hi_lt]
  -- Key: The list (List.ofFn a) is already sorted in decreasing order
  have hsorted : List.Pairwise (· ≥ ·) (List.ofFn a) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simp only [List.get_ofFn]
    exact ha (le_of_lt hij)
  -- The multiset equals List.ofFn a as a multiset
  have hmulti : Finset.univ.val.map a = ↑(List.ofFn a) := by
    simp only [Finset.univ, Fintype.elems, Multiset.map_coe]
    rw [List.ofFn_eq_map]
  -- mergeSort of a sorted list is the same list
  have hmerge : List.mergeSort (List.ofFn a) (fun x y => x ≥ y) = List.ofFn a := by
    apply List.mergeSort_eq_self
    exact hsorted
  -- The sorted list equals List.ofFn a
  have hsort_eq : (Finset.univ.val.map a).sort (· ≥ ·) = List.ofFn a := by
    rw [hmulti]
    simp only [Multiset.coe_sort]
    exact hmerge
  -- Use List.get_of_eq to handle the dependent type
  have hi_lt' : i.val < (List.ofFn a).length := by simp
  show ((Finset.univ.val.map a).sort (· ≥ ·)).get ⟨i.val, hi_lt⟩ = a i
  rw [List.get_of_eq hsort_eq, List.get_ofFn, Fin.cast_mk]

/-- Sorting an NPartition's parts returns the same NPartition. -/
theorem sortTuple_of_NPartition (mu : NPartition N) :
    sortTuple mu.parts = mu := by
  ext
  exact congrFun (sortTuple_of_antitone mu.parts mu.antitone) _

/-!
## Addition of N-partitions

The `Add (NPartition N)` instance and related lemmas (`add_size`, `add_comm`, `add_zero`,
`zero_add`, `add_assoc`) are provided by the canonical `NPartition.lean` file.

The canonical definition uses component-wise addition (without sorting), which is equivalent
to sorting the sum for N-partitions since the sum of two antitone functions is antitone.
This is witnessed by `sortTuple_of_NPartition`.
-/
/-!
### Helper lemmas for symmetry proof

The following lemmas establish that sorting is invariant under permutation of the input,
which is the key insight for proving that monomial symmetric polynomials are symmetric.
-/


/-- The multiset of values is preserved under permutation of the domain.
    This is the key lemma showing that permuting the indices of a tuple
    doesn't change its multiset of values. -/
theorem map_comp_perm_eq (a : Fin N → ℕ) (σ : Perm (Fin N)) :
    (Finset.univ.val.map (a ∘ σ)) = (Finset.univ.val.map a) := by
  rw [← Multiset.map_map]
  congr 1
  have h : Multiset.map σ (Finset.univ : Finset (Fin N)).val = (Finset.univ : Finset (Fin N)).val := by
    ext x
    simp only [Multiset.count_map]
    have key : (Multiset.filter (fun y => x = σ y) (Finset.univ : Finset (Fin N)).val).card = 1 := by
      have h1 : (Multiset.filter (fun y => x = σ y) (Finset.univ : Finset (Fin N)).val) =
                (Finset.filter (fun y => x = σ y) (Finset.univ : Finset (Fin N))).val := rfl
      rw [h1, Finset.card_val, Finset.card_eq_one]
      use σ⁻¹ x
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hy; exact σ.injective (by simp [hy])
      · intro hy; simp [hy]
    rw [key, Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin N)).nodup]
    exact Finset.mem_univ x
  exact h

/-- Sorting is invariant under permutation of the input tuple.
    This is the key insight: sortTuple (a ∘ σ) = sortTuple a for any permutation σ,
    because sorting only depends on the multiset of values, not their order. -/
theorem sortTuple_comp_perm (a : Fin N → ℕ) (σ : Perm (Fin N)) :
    sortTuple (a ∘ σ) = sortTuple a := by
  ext i
  unfold sortTuple
  simp only
  rw [map_comp_perm_eq a σ]

/-- Applying rename σ to a monomial x^a gives x^(a ∘ σ⁻¹). -/
theorem rename_monomialExp (σ : Perm (Fin N)) (a : Fin N → ℕ) :
    rename σ (monomialExp (R := R) a) = monomialExp (a ∘ σ.symm) := by
  simp only [monomialExp]
  rw [map_prod]
  conv_lhs =>
    arg 2
    ext i
    rw [map_pow, rename_X]
  rw [← Finset.prod_equiv σ.symm]
  · simp
  · intro i _
    simp [Function.comp]

end SymmetricFunctions
end AlgebraicCombinatorics
