/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Theorem.Combinatorics.Young.MonomialSymmetric.Part2
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

/-- The equivalence between partitions of length ≤ N that sum to n and N-partitions of size n.
    (Proposition prop.sf.Npar-as-par)

    This provides the bijection:
    - Forward: pad partition with zeros to get N-partition
    - Backward: remove trailing zeros from N-partition to get partition

    Note: We state this as an `Equiv` which is the proper way to express a bijection in Mathlib. -/
noncomputable def equivPartition (n : ℕ) :
    {p : Nat.Partition n // Multiset.card p.parts ≤ N} ≃
    {mu : NPartition N // mu.size = n} where
  toFun := fun ⟨p, hp⟩ => ⟨ofPartition p hp, ofPartition_size p hp⟩
  invFun := fun ⟨mu, hmu⟩ =>
    let p' : Nat.Partition mu.size := mu.toPartition
    let hp' : Multiset.card p'.parts ≤ N := toPartition_card_le mu
    ⟨hmu ▸ p', by subst hmu; exact hp'⟩
  left_inv := by
    simp only
    intro ⟨p, hp⟩
    simp only [Subtype.mk.injEq]
    -- Need: toPartition (ofPartition p hp) = p (up to the size equality cast)
    -- The key is that the parts multiset is preserved
    have hparts := toPartition_ofPartition_parts p hp
    apply Nat.Partition.ext_iff.mpr
    rw [Nat.Partition.parts_cast, hparts]
  right_inv := by
    intro ⟨mu, hmu⟩
    simp only [Subtype.mk.injEq]
    subst hmu
    ext i
    simp only [_root_.NPartition.ofPartition, _root_.NPartition.toPartition]
    have h_univ_map : (Finset.univ.val.map mu.parts : Multiset ℕ) = ↑(List.ofFn mu.parts) :=
      finset_univ_val_map_eq_ofFn mu.parts
    have h_sort_eq : (↑((List.ofFn mu.parts).filter (· ≠ 0)) : Multiset ℕ).sort (· ≥ ·) =
        (List.ofFn mu.parts).filter (· ≠ 0) :=
      sort_filter_nonzero_eq_self mu.parts mu.antitone
    have h1 : ((Finset.univ.val.map mu.parts).filter (· ≠ 0)).sort (· ≥ ·) = 
              (List.ofFn mu.parts).filter (· ≠ 0) := by
      rw [h_univ_map, Multiset.filter_coe, h_sort_eq]
    simp only [h1]
    split_ifs with hi
    · -- Case: i < filter.length, need: filter.get = mu.parts i
      -- The goal has .get instead of [·], so we need to convert
      have h_filter_take := filter_nonzero_eq_take mu.parts mu.antitone
      have h_k_le_N : ((List.ofFn mu.parts).filter (· ≠ 0)).length ≤ N := by
        calc ((List.ofFn mu.parts).filter (· ≠ 0)).length
            ≤ (List.ofFn mu.parts).length := List.length_filter_le _ _
          _ = N := List.length_ofFn
      -- Cast hi to the take version
      have hi' : i.val < ((List.ofFn mu.parts).take ((List.ofFn mu.parts).filter (· ≠ 0)).length).length := by
        rw [List.length_take, List.length_ofFn]
        exact Nat.lt_min.mpr ⟨hi, i.isLt⟩
      -- Rewrite filter.get using filter = take k
      have list_get_eq : ∀ (l1 l2 : List ℕ) (h12 : l1 = l2) (j : ℕ) (hj1 : j < l1.length) (hj2 : j < l2.length),
          l1.get ⟨j, hj1⟩ = l2.get ⟨j, hj2⟩ := by
        intro l1 l2 h12 j hj1 hj2
        subst h12
        rfl
      -- Use h1 to rewrite the goal
      have h2 : (((Finset.univ.val.map mu.parts).filter (· ≠ 0)).sort (· ≥ ·)).get ⟨i.val, by rw [h1]; exact hi⟩ =
                ((List.ofFn mu.parts).filter (· ≠ 0)).get ⟨i.val, hi⟩ :=
        list_get_eq _ _ h1 _ _ hi
      rw [h2]
      -- Now use filter = take k
      have h3 : ((List.ofFn mu.parts).filter (· ≠ 0)).get ⟨i.val, hi⟩ =
                ((List.ofFn mu.parts).take ((List.ofFn mu.parts).filter (· ≠ 0)).length).get ⟨i.val, hi'⟩ :=
        list_get_eq _ _ h_filter_take _ hi hi'
      rw [h3]
      simp only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn]
    · -- Case: i ≥ filter.length, need: 0 = mu.parts i
      have hge : ¬(i.val < ((List.ofFn mu.parts).filter (· ≠ 0)).length) := hi
      push Not at hge
      have heq : mu.parts i = 0 := by
        by_contra hne
        have : i.val < ((List.ofFn mu.parts).filter (· ≠ 0)).length :=
          (lt_filter_length_iff_ne_zero mu.parts mu.antitone i).mpr hne
        omega
      exact heq.symm

end NPartition

/-!
## Monomials and sorting (Definition def.sf.sort)
-/


/-- The monomial x^a = x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N} for a tuple a ∈ ℕ^N.
    (Definition def.sf.sort (a)) -/
noncomputable def monomialExp (a : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  ∏ i, X i ^ a i

/-- Sort a tuple in weakly decreasing order to get an N-partition.
    (Definition def.sf.sort (b)) -/
def sortTuple (a : Fin N → ℕ) : NPartition N where
  parts := fun i =>
    let sorted := (Finset.univ.val.map a).sort (· ≥ ·)
    if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0
  antitone := by
    intro i j hij
    simp only
    split_ifs with hi hj hj
    · have hsorted : ((Finset.univ.val.map a).sort (· ≥ ·)).Pairwise (· ≥ ·) :=
        Multiset.pairwise_sort (r := (· ≥ ·)) (Finset.univ.val.map a)
      exact List.Pairwise.rel_get_of_le hsorted hij
    · omega
    · exact Nat.zero_le _
    · exact le_refl 0

end SymmetricFunctions
end AlgebraicCombinatorics
