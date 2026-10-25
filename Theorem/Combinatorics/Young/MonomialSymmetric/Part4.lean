/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.MonomialSymmetric.Part2
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

/-- Permutation preserves membership in sortPreimage.
    If a is in the preimage of μ under sorting, then so is a ∘ σ.symm. -/
theorem mem_sortPreimage_comp_perm {a : Fin N → ℕ} {mu : NPartition N} (σ : Perm (Fin N))
    (ha : a ∈ sortPreimage mu) : (a ∘ σ.symm) ∈ sortPreimage mu := by
  simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset] at ha ⊢
  refine ⟨?_, ?_⟩
  · intro i
    have := ha.1 (σ.symm i)
    simp only [Finset.mem_range] at this ⊢
    exact this
  · rw [sortTuple_comp_perm, ha.2]

/-- Permutation preserves membership in sortPreimage (variant with σ instead of σ.symm). -/
theorem mem_sortPreimage_comp_perm' {a : Fin N → ℕ} {mu : NPartition N} (σ : Perm (Fin N))
    (ha : a ∈ sortPreimage mu) : (a ∘ σ) ∈ sortPreimage mu := by
  exact mem_sortPreimage_comp_perm (σ := σ.symm) ha

/-- The monomial symmetric polynomial is symmetric.
    (Follows from Definition def.sf.m)

    The proof uses the fact that:
    1. rename σ (monomialExp a) = monomialExp (a ∘ σ⁻¹)
    2. sortTuple (a ∘ σ) = sortTuple a for any permutation σ
    3. Therefore the sum over sortPreimage μ is invariant under rename σ -/
theorem monomialSymm_isSymmetric (mu : NPartition N) :
    (monomialSymm mu : MvPolynomial (Fin N) R).IsSymmetric := by
  intro σ
  simp only [monomialSymm]
  rw [map_sum]
  -- Rewrite each term using rename_monomialExp
  conv_lhs =>
    arg 2
    ext a
    rw [rename_monomialExp]
  -- The sum ∑ a ∈ sortPreimage mu, monomialExp (a ∘ σ.symm) equals
  -- ∑ a ∈ sortPreimage mu, monomialExp a because composition with σ.symm
  -- is a bijection on sortPreimage mu
  exact Finset.sum_bij' (fun a _ => a ∘ σ.symm) (fun b _ => b ∘ σ)
    (fun a ha => mem_sortPreimage_comp_perm σ ha)
    (fun b hb => mem_sortPreimage_comp_perm' σ hb)
    (fun a _ => by ext i; exact congrArg a (σ.symm_apply_apply i))
    (fun b _ => by ext i; exact congrArg b (σ.apply_symm_apply i))
    (fun a _ => rfl)

/-- The parts of an N-partition belong to its sortPreimage.
    This is because sorting an already sorted (antitone) tuple gives the same tuple. -/
theorem parts_mem_sortPreimage (mu : NPartition N) : mu.parts ∈ sortPreimage mu := by
  simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro i
    simp only [Finset.mem_range]
    calc mu.parts i ≤ mu.size := NPartition.parts_le_size mu i
      _ < mu.size + 1 := Nat.lt_succ_self _
  · exact sortTuple_of_NPartition mu

/-- The coefficient of x^{μ.parts} in m_μ is 1.
    This is because μ.parts is the unique element of sortPreimage μ that equals μ.parts. -/
theorem monomialSymm_coeff_self (mu : NPartition N) :
    coeff (Finsupp.equivFunOnFinite.symm mu.parts) (monomialSymm mu : MvPolynomial (Fin N) R) = 1 := by
  simp only [monomialSymm, coeff, MvPolynomial.coeff_sum]
  have h : ∑ a ∈ sortPreimage mu,
      (monomialExp (R := R) a).coeff (Finsupp.equivFunOnFinite.symm mu.parts) =
      (monomialExp (R := R) mu.parts).coeff (Finsupp.equivFunOnFinite.symm mu.parts) := by
    rw [Finset.sum_eq_single_of_mem mu.parts (parts_mem_sortPreimage mu)]
    intro b _ hne
    simp only [monomialExp_eq_monomial, coeff_monomial, ite_eq_right_iff]
    intro heq
    exfalso
    apply hne
    exact (Finsupp.equivFunOnFinite.symm.injective heq.symm).symm
  rw [h]
  simp [monomialExp_eq_monomial, coeff_monomial]

/-- The coefficient of x^{μ.parts} in m_ν is 0 when μ ≠ ν.
    This is because the only monomial in m_ν with exponent sorting to ν must have
    exponent ν.parts (when looking at the sorted exponent), not μ.parts. -/
theorem monomialSymm_coeff_ne (mu nu : NPartition N) (h : mu ≠ nu) :
    coeff (Finsupp.equivFunOnFinite.symm mu.parts) (monomialSymm nu : MvPolynomial (Fin N) R) = 0 := by
  simp only [monomialSymm, coeff, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro a ha
  simp only [monomialExp_eq_monomial, coeff_monomial, ite_eq_right_iff]
  intro heq
  exfalso
  simp only [sortPreimage, Finset.mem_filter] at ha
  have ha_sort : sortTuple a = nu := ha.2
  have heq' : a = mu.parts := Finsupp.equivFunOnFinite.symm.injective heq
  rw [heq', sortTuple_of_NPartition] at ha_sort
  exact h ha_sort

end SymmetricFunctions
end AlgebraicCombinatorics
