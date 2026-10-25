/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.MonomialSymmetric.Part5
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

/-- The monomial x^a is homogeneous of degree ∑ᵢ aᵢ. -/
theorem monomialExp_isHomogeneous (a : Fin N → ℕ) :
    (monomialExp a : MvPolynomial (Fin N) R).IsHomogeneous (∑ i, a i) := by
  simp only [monomialExp]
  apply MvPolynomial.IsHomogeneous.prod
  intro i _
  have h1 : (X i : MvPolynomial (Fin N) R).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X R i
  have h2 := h1.pow (a i)
  convert h2 using 1
  ring

/-- The monomial symmetric polynomial m_μ is homogeneous of degree |μ|. -/
theorem monomialSymm_isHomogeneous (mu : NPartition N) :
    (monomialSymm mu : MvPolynomial (Fin N) R).IsHomogeneous mu.size := by
  simp only [monomialSymm]
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  simp only [sortPreimage, Finset.mem_filter] at ha
  have heq : (sortTuple a).size = ∑ i, a i := sortTuple_size a
  rw [ha.2] at heq
  rw [heq]
  exact monomialExp_isHomogeneous a

/-- The homogeneous component of m_μ of degree n is m_μ if |μ| = n, and 0 otherwise. -/
theorem homogeneousComponent_monomialSymm (mu : NPartition N) (n : ℕ) :
    homogeneousComponent n (monomialSymm (R := R) mu) =
    if mu.size = n then monomialSymm mu else 0 := by
  rw [homogeneousComponent_of_mem (monomialSymm_isHomogeneous mu)]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

/-- The monomial symmetric polynomials of size n span 𝒮_n.
    (Theorem thm.sf.m-basis (d), spanning part)

    Label: thm.sf.m-basis.d.span -/
theorem monomialSymm_homogeneous_spans (n : ℕ) :
    ∀ f ∈ symmHomogeneous N R n,
    f ∈ Submodule.span R (Set.range (fun mu : {nu : NPartition N // nu.size = n} =>
      monomialSymm mu.val)) := by
  intro f hf
  obtain ⟨hf_symm, hf_hom⟩ := hf
  -- f is symmetric, so it's in the span of all monomialSymm
  have h := monomialSymm_spans f hf_symm
  -- Since f is homogeneous of degree n, homogeneousComponent n f = f
  have hf_comp : homogeneousComponent n f = f := by
    rw [homogeneousComponent_of_mem hf_hom]
    simp
  -- Apply homogeneousComponent n to get f in span of (homogeneousComponent n '' S)
  let S := Set.range (fun mu : NPartition N => (monomialSymm mu : MvPolynomial (Fin N) R))
  have h2 : f ∈ Submodule.span R ((homogeneousComponent n) '' S) := by
    rw [← hf_comp]
    have := Submodule.mem_map_of_mem (f := homogeneousComponent n) h
    rw [Submodule.map_span] at this
    exact this
  -- Now show that the image is contained in the span of the restricted range
  let T := Set.range (fun mu : {nu : NPartition N // nu.size = n} =>
    (monomialSymm mu.val : MvPolynomial (Fin N) R))
  have h3 : (homogeneousComponent n) '' S ⊆ (Submodule.span R T : Set (MvPolynomial (Fin N) R)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨mu, rfl⟩ := hy
    rw [homogeneousComponent_monomialSymm]
    split_ifs with hmu
    · -- mu.size = n, so monomialSymm mu is in the span
      exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨mu, hmu⟩, rfl⟩)
    · -- mu.size ≠ n, so result is 0, which is in any submodule
      exact Submodule.zero_mem _
  have h4 : Submodule.span R ((homogeneousComponent n) '' S) ≤ Submodule.span R T := by
    apply Submodule.span_le.mpr h3
  exact h4 h2

/-- The monomial symmetric polynomials of size n are linearly independent.
    (Theorem thm.sf.m-basis (d), linear independence part)

    This follows from the fact that no two m_μ share any monomials, and each m_μ
    contains at least one monomial.

    Label: thm.sf.m-basis.d.indep -/
theorem monomialSymm_homogeneous_linearIndependent (n : ℕ) :
    LinearIndependent R (fun mu : {nu : NPartition N // nu.size = n} =>
      (monomialSymm mu.val : MvPolynomial (Fin N) R)) := by
  -- Use linearIndependent_iff'ₛ which works for semirings
  rw [linearIndependent_iff'ₛ]
  intro s f g hfg i hi
  -- Extract the coefficient of i.parts from the sum
  have key : coeff (Finsupp.equivFunOnFinite.symm i.val.parts)
      (∑ j ∈ s, f j • monomialSymm j.val : MvPolynomial (Fin N) R) =
      coeff (Finsupp.equivFunOnFinite.symm i.val.parts)
      (∑ j ∈ s, g j • monomialSymm j.val : MvPolynomial (Fin N) R) := by
    rw [hfg]
  simp only [coeff_sum, coeff_smul] at key
  have hf : ∑ j ∈ s, f j • coeff (Finsupp.equivFunOnFinite.symm i.val.parts)
      (monomialSymm j.val : MvPolynomial (Fin N) R) = f i := by
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp [monomialSymm_coeff_self]
    · intro j hj hne
      simp only [smul_eq_mul]
      have hne' : i.val ≠ j.val := fun heq => hne (Subtype.ext heq.symm)
      rw [monomialSymm_coeff_ne i.val j.val hne', mul_zero]
  have hg : ∑ j ∈ s, g j • coeff (Finsupp.equivFunOnFinite.symm i.val.parts)
      (monomialSymm j.val : MvPolynomial (Fin N) R) = g i := by
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp [monomialSymm_coeff_self]
    · intro j hj hne
      simp only [smul_eq_mul]
      have hne' : i.val ≠ j.val := fun heq => hne (Subtype.ext heq.symm)
      rw [monomialSymm_coeff_ne i.val j.val hne', mul_zero]
  rw [hf, hg] at key
  exact key

/-- Linear independence in a submodule follows from linear independence of the 
    coerced elements in the ambient module. -/
theorem linearIndependent_submodule_of_linearIndependent 
    {S : Submodule R (MvPolynomial (Fin N) R)} {ι : Type*} (v : ι → S) 
    (hli : LinearIndependent R (fun i => (v i : MvPolynomial (Fin N) R))) :
    LinearIndependent R v := by
  rw [linearIndependent_iff'ₛ] at hli ⊢
  intro s f g hfg i hi
  have h : ∑ j ∈ s, f j • (v j : MvPolynomial (Fin N) R) = 
           ∑ j ∈ s, g j • (v j : MvPolynomial (Fin N) R) := by
    have := congrArg (Submodule.subtype S) hfg
    simp only [map_sum, map_smul, Submodule.coe_subtype] at this
    exact this
  exact hli s f g h i hi

/-- If elements of a submodule span the submodule (when coerced to the ambient module),
    then they span the submodule as a module. -/
theorem span_eq_top_of_subtype_span
    {S : Submodule R (MvPolynomial (Fin N) R)} {ι : Type*} (v : ι → S) 
    (hsp : ∀ x : S, (x : MvPolynomial (Fin N) R) ∈ 
           Submodule.span R (Set.range (fun i => (v i : MvPolynomial (Fin N) R)))) :
    ⊤ ≤ Submodule.span R (Set.range v) := by
  intro x _
  specialize hsp x
  have key : Submodule.map (Submodule.subtype S) (Submodule.span R (Set.range v)) = 
             Submodule.span R (Set.range (fun i => (v i : MvPolynomial (Fin N) R))) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Submodule.coe_subtype]
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  rw [← key] at hsp
  rw [Submodule.mem_map] at hsp
  obtain ⟨y, hy, hxy⟩ := hsp
  have hyx : y = x := Subtype.ext hxy
  rw [← hyx]
  exact hy

/-- monomialSymm maps into symmHomogeneous when the size matches. -/
theorem monomialSymm_mem_symmHomogeneous' (mu : NPartition N) (n : ℕ) (h : mu.size = n) :
    (monomialSymm mu : MvPolynomial (Fin N) R) ∈ symmHomogeneous N R n := by
  constructor
  · exact monomialSymm_isSymmetric mu
  · rw [← h]
    exact monomialSymm_isHomogeneous mu

end SymmetricFunctions
end AlgebraicCombinatorics
