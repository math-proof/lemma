/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.MonomialSymmetric.Part4
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

/-- Helper lemma for constructing permutations from equal fiber cardinalities. -/
theorem fiber_equiv_val_eq {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    (a b : α → β) (hcount : ∀ v, (Finset.univ.filter (fun i => a i = v)).card =
                                  (Finset.univ.filter (fun i => b i = v)).card)
    (v w : β) (hvw : v = w) (j : α)
    (hj_v : j ∈ Finset.univ.filter (fun k => b k = v))
    (hj_w : j ∈ Finset.univ.filter (fun k => b k = w)) :
    ((Finset.equivOfCardEq (hcount v)).symm ⟨j, hj_v⟩).val =
    ((Finset.equivOfCardEq (hcount w)).symm ⟨j, hj_w⟩).val := by
  subst hvw
  rfl

/-- Key combinatorial fact: if two functions from a finite type have the same
    multiset of values, then they differ by a permutation. -/
theorem exists_perm_of_map_eq {α : Type*} [Fintype α] [DecidableEq α] {β : Type*} [DecidableEq β]
    (a b : α → β) (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ σ : Perm α, ∀ i, b i = a (σ i) := by
  classical
  have hcount : ∀ v, (Finset.univ.filter (fun i => a i = v)).card =
                     (Finset.univ.filter (fun i => b i = v)).card := by
    intro v
    have ha : (Finset.univ.filter (fun i => a i = v)).card = Multiset.count v (Finset.univ.val.map a) := by
      rw [Multiset.count_map]
      have h : Multiset.filter (fun a_1 => v = a a_1) Finset.univ.val =
               Multiset.filter (fun a_1 => a a_1 = v) Finset.univ.val := by
        congr 1; ext x; exact eq_comm
      rw [h]; rfl
    have hb : (Finset.univ.filter (fun i => b i = v)).card = Multiset.count v (Finset.univ.val.map b) := by
      rw [Multiset.count_map]
      have h : Multiset.filter (fun a_1 => v = b a_1) Finset.univ.val =
               Multiset.filter (fun a_1 => b a_1 = v) Finset.univ.val := by
        congr 1; ext x; exact eq_comm
      rw [h]; rfl
    rw [ha, hb, h]
  let fiber_equiv : ∀ v, (Finset.univ.filter (fun i => a i = v)) ≃
                         (Finset.univ.filter (fun i => b i = v)) :=
    fun v => Finset.equivOfCardEq (hcount v)
  let σ : α → α := fun i =>
    let hi : i ∈ Finset.univ.filter (fun j => b j = b i) := by simp
    ((fiber_equiv (b i)).symm ⟨i, hi⟩).val
  have hσ_prop : ∀ i, a (σ i) = b i := by
    intro i
    simp only [σ]
    have hi : i ∈ Finset.univ.filter (fun j => b j = b i) := by simp
    have hσi := ((fiber_equiv (b i)).symm ⟨i, hi⟩).prop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσi
    exact hσi
  have hσ_inj : Function.Injective σ := by
    intro i j hij
    have hbi_eq_bj : b i = b j := by
      rw [← hσ_prop i, ← hσ_prop j, hij]
    have hi' : i ∈ Finset.univ.filter (fun k => b k = b i) := by simp
    have hj'' : j ∈ Finset.univ.filter (fun k => b k = b i) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, hbi_eq_bj.symm⟩
    have hinj := (fiber_equiv (b i)).symm.injective
    have heq : (⟨i, hi'⟩ : (Finset.univ.filter (fun k => b k = b i))) =
               (⟨j, hj''⟩ : (Finset.univ.filter (fun k => b k = b i))) := by
      apply hinj
      apply Subtype.ext
      simp only [σ] at hij
      have hbj_eq_bi : b j = b i := hbi_eq_bj.symm
      have h1 : ((fiber_equiv (b i)).symm ⟨i, hi'⟩).val = σ i := rfl
      have h2 : σ j = ((fiber_equiv (b j)).symm ⟨j, by simp⟩).val := rfl
      have h3 : ((fiber_equiv (b j)).symm ⟨j, by simp⟩).val =
                ((fiber_equiv (b i)).symm ⟨j, hj''⟩).val :=
        fiber_equiv_val_eq a b hcount (b j) (b i) hbj_eq_bi j (by simp) hj''
      calc ((fiber_equiv (b i)).symm ⟨i, hi'⟩).val
          = σ i := h1
        _ = σ j := hij
        _ = ((fiber_equiv (b j)).symm ⟨j, by simp⟩).val := h2
        _ = ((fiber_equiv (b i)).symm ⟨j, hj''⟩).val := h3
    simp only [Subtype.mk.injEq] at heq
    exact heq
  have hσ_bij : Function.Bijective σ := ⟨hσ_inj, Finite.surjective_of_injective hσ_inj⟩
  use Equiv.ofBijective σ hσ_bij
  intro i
  simp only [Equiv.ofBijective_apply]
  exact (hσ_prop i).symm

/-- If two tuples have the same sort, they have the same multiset of values. -/
theorem sortTuple_eq_implies_multiset_eq (a b : Fin N → ℕ)
    (h : sortTuple a = sortTuple b) :
    (Finset.univ.val.map a) = (Finset.univ.val.map b) := by
  have hlen_a : ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have hlen_b : ((Finset.univ.val.map b).sort (· ≥ ·)).length = N := by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have h_parts : ∀ i : Fin N, (sortTuple a).parts i = (sortTuple b).parts i := by
    intro i
    rw [h]
  have h_sorted_eq : (Finset.univ.val.map a).sort (· ≥ ·) = (Finset.univ.val.map b).sort (· ≥ ·) := by
    apply List.ext_get
    · rw [hlen_a, hlen_b]
    · intro n h1 h2
      have hn : n < N := by rw [← hlen_a]; exact h1
      have hp := h_parts ⟨n, hn⟩
      simp only [sortTuple] at hp
      simp only [hlen_a, hn, ↓reduceDIte] at hp
      have h2' : n < ((Finset.univ.val.map b).sort (· ≥ ·)).length := by rw [hlen_b]; exact hn
      simp only [h2', ↓reduceDIte] at hp
      exact hp
  have ha : ↑((Finset.univ.val.map a).sort (· ≥ ·)) = (Finset.univ.val.map a) :=
    Multiset.sort_eq _ _
  have hb : ↑((Finset.univ.val.map b).sort (· ≥ ·)) = (Finset.univ.val.map b) :=
    Multiset.sort_eq _ _
  rw [← ha, ← hb, h_sorted_eq]

/-- Coefficients are equal for exponents with the same sort (for symmetric polynomials).
    This follows from the fact that two tuples with the same sort differ by a permutation,
    and symmetric polynomials have permutation-invariant coefficients.

    The proof requires the combinatorial fact that equal sorted multisets implies
    the existence of a permutation relating the two tuples. -/
theorem coeff_eq_of_same_sort (f : MvPolynomial (Fin N) R) (hf : f.IsSymmetric)
    (d₁ d₂ : Fin N →₀ ℕ) (h : sortTupleFinsupp d₁ = sortTupleFinsupp d₂) :
    coeff d₁ f = coeff d₂ f := by
  -- Step 1: sortTupleFinsupp equality implies multiset equality
  unfold sortTupleFinsupp at h
  have h_multiset_eq := sortTuple_eq_implies_multiset_eq _ _ h
  -- Step 2: There exists a permutation σ such that d₂ i = d₁ (σ i)
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq _ _ h_multiset_eq
  -- Step 3: d₂ = Finsupp.mapDomain σ.symm d₁
  have h_d₂_eq : d₂ = Finsupp.mapDomain σ.symm d₁ := by
    ext i
    have h1 : d₂ i = d₁ (σ i) := hσ i
    have h2 : (Finsupp.mapDomain σ.symm d₁) i = d₁ (σ i) := by
      rw [Finsupp.mapDomain_equiv_apply]
      simp
    rw [h1, ← h2]
  -- Step 4: Apply coeff_perm_eq_of_symmetric
  rw [h_d₂_eq]
  exact (coeff_perm_eq_of_symmetric f hf d₁ σ.symm).symm

/-- The monomial symmetric polynomials span the symmetric polynomials.
    (Theorem thm.sf.m-basis (a), spanning part)

    The proof proceeds by:
    1. Writing f as a sum of monomials grouped by their sort
    2. For symmetric f, all monomials with the same sort have the same coefficient
    3. Factoring out the common coefficient from each group
    4. Showing that the sum of monomials in each group equals monomialSymm μ

    Label: thm.sf.m-basis.a.span -/
theorem monomialSymm_spans :
    ∀ f : MvPolynomial (Fin N) R, f.IsSymmetric →
    f ∈ Submodule.span R (Set.range (fun mu : NPartition N => monomialSymm mu)) := by
  intro f hf
  -- Write f as sum of monomials
  have hf_sum : f = ∑ d ∈ f.support, monomial d (coeff d f) := f.as_sum
  rw [hf_sum]
  -- Partition by sortTupleFinsupp
  rw [sum_partition f.support sortTupleFinsupp (fun d => monomial d (coeff d f))]
  -- Show each partition class is in the span
  apply Submodule.sum_mem
  intro μ hμ
  -- Get a representative element from this partition class
  simp only [mem_image] at hμ
  obtain ⟨d₀, hd₀_mem, hd₀_sort⟩ := hμ
  -- All elements in this class have the same coefficient as d₀
  have hcoeff_eq : ∀ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ),
      coeff d f = coeff d₀ f := by
    intro d hd
    simp only [mem_filter] at hd
    rw [← hd₀_sort] at hd
    exact coeff_eq_of_same_sort f hf d d₀ hd.2
  -- Factor out the common coefficient
  have h_factor : ∑ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ), monomial d (coeff d f) =
      coeff d₀ f • ∑ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ), monomial d 1 := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hcoeff_eq d hd, smul_monomial, smul_eq_mul, mul_one]
  rw [h_factor]
  apply Submodule.smul_mem
  -- The sum ∑_{d : sort d = μ, d ∈ support f} monomial d 1 equals monomialSymm μ
  -- for symmetric f. This is because:
  -- 1. For symmetric f, support is closed under permutation
  -- 2. Two Finsupps have the same sort iff they are permutations of each other
  -- 3. So if any d with sort μ is in support, ALL d with sort μ are in support
  -- 4. Therefore the filter set equals sortPreimage μ (converted to Finsupp)
  --
  -- We show the sum equals monomialSymm μ, then use subset_span.
  -- monomialSymm μ = ∑ a ∈ sortPreimage μ, monomialExp a
  --                = ∑ a ∈ sortPreimage μ, monomial (equivFunOnFinite.symm a) 1
  -- We establish a bijection between the filter set and sortPreimage μ.
  
  -- Helper: sortTupleFinsupp of equivFunOnFinite.symm a equals sortTuple a
  have h_sort_equiv : ∀ a : Fin N → ℕ, 
      sortTupleFinsupp (Finsupp.equivFunOnFinite.symm a) = sortTuple a := fun a => by
    unfold sortTupleFinsupp
    simp only [Equiv.apply_symm_apply]
  
  -- Helper: sortTupleFinsupp d = μ implies d.sum = μ.size
  have h_sum_eq_size : ∀ d : Fin N →₀ ℕ, sortTupleFinsupp d = μ → 
      d.sum (fun _ n => n) = μ.size := fun d hd => by
    have h1 : (sortTupleFinsupp d).size = d.sum (fun _ n => n) := by
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
    rw [hd] at h1
    exact h1.symm
  
  -- Helper: entries of a Finsupp are bounded by their sum
  have h_entry_le_sum : ∀ (d : Fin N →₀ ℕ) (i : Fin N), d i ≤ d.sum (fun _ n => n) := 
    fun d i => by
      by_cases hi : i ∈ d.support
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
      · simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hi
        simp [hi]
  
  -- Helper: d in filter implies equivFunOnFinite d ∈ sortPreimage μ
  have h_filter_to_preimage : ∀ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ),
      Finsupp.equivFunOnFinite d ∈ sortPreimage μ := fun d hd => by
    simp only [mem_filter] at hd
    simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · intro i
      have h1 : d i ≤ d.sum (fun _ n => n) := h_entry_le_sum d i
      have h2 : d.sum (fun _ n => n) = μ.size := h_sum_eq_size d hd.2
      calc Finsupp.equivFunOnFinite d i = d i := rfl
        _ ≤ d.sum (fun _ n => n) := h1
        _ = μ.size := h2
        _ < μ.size + 1 := Nat.lt_succ_self _
    · unfold sortTupleFinsupp at hd
      exact hd.2
  
  -- Helper: a ∈ sortPreimage μ implies equivFunOnFinite.symm a ∈ filter
  have h_preimage_to_filter : ∀ a ∈ sortPreimage μ,
      Finsupp.equivFunOnFinite.symm a ∈ f.support.filter (fun d => sortTupleFinsupp d = μ) := 
    fun a ha => by
      simp only [mem_filter]
      constructor
      · -- Show equivFunOnFinite.symm a ∈ f.support
        -- This follows from: coeff (equivFunOnFinite.symm a) f = coeff d₀ f ≠ 0
        rw [mem_support_iff] at hd₀_mem ⊢
        have h_sort_eq : sortTupleFinsupp (Finsupp.equivFunOnFinite.symm a) =
                         sortTupleFinsupp d₀ := by
          rw [h_sort_equiv]
          simp only [sortPreimage, Finset.mem_filter] at ha
          rw [ha.2, hd₀_sort]
        have h_coeff_eq := coeff_eq_of_same_sort f hf
          (Finsupp.equivFunOnFinite.symm a) d₀ h_sort_eq
        simpa [h_coeff_eq] using hd₀_mem
      · -- Show sortTupleFinsupp (equivFunOnFinite.symm a) = μ
        rw [h_sort_equiv]
        simp only [sortPreimage, Finset.mem_filter] at ha
        exact ha.2
  
  -- Now show the sum equals monomialSymm μ using sum_bij'
  have h_sum_eq : ∑ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ), 
      (monomial d (1 : R) : MvPolynomial (Fin N) R) = monomialSymm μ := by
    simp only [monomialSymm]
    symm
    exact Finset.sum_bij' 
      (fun a _ => Finsupp.equivFunOnFinite.symm a)
      (fun d _ => Finsupp.equivFunOnFinite d)
      h_preimage_to_filter
      h_filter_to_preimage
      (fun a _ => by simp)
      (fun d _ => by simp)
      (fun a _ => by rw [monomialExp_eq_monomial])
  
  have hmem : (monomialSymm μ : MvPolynomial (Fin N) R) ∈ 
      Submodule.span R (Set.range (fun mu : NPartition N => monomialSymm mu)) := 
    Submodule.subset_span ⟨μ, rfl⟩
  convert hmem using 1

end SymmetricFunctions
end AlgebraicCombinatorics
