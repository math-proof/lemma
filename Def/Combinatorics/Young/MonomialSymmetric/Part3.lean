/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Theorem.Combinatorics.Young.MonomialSymmetric.Part4
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
## Elementary, homogeneous, and power sum via monomial symmetric polynomials
    (Proposition prop.sf.ehp-through-m)
-/


/-- The N-partition (1, 1, ..., 1, 0, 0, ..., 0) with n ones and N-n zeros. -/
def onesThenZeros (n : ℕ) (_hn : n ≤ N) : NPartition N where
  parts := fun i => if i.val < n then 1 else 0
  antitone := by
    intro i j hij
    simp only
    split_ifs with hi hj hj
    · exact le_refl 1
    · omega
    · exact Nat.zero_le _
    · exact le_refl 0

/-- The N-partition (n, 0, 0, ..., 0) with n in the first position and zeros elsewhere. -/
def singletonPartition (n : ℕ) (_hN : 0 < N) : NPartition N where
  parts := fun i => if i.val = 0 then n else 0
  antitone := by
    intro i j hij
    -- Goal: (if j.val = 0 then n else 0) ≤ (if i.val = 0 then n else 0)
    simp only
    split_ifs with h1 h2
    · -- h1 : j.val = 0, h2 : i.val = 0
      exact le_refl n
    · -- h1 : j.val = 0, h2 : ¬ i.val = 0
      -- Goal: n ≤ 0
      -- But j.val = 0 and i ≤ j means i.val ≤ 0, so i.val = 0, contradiction with h2
      have : i.val ≤ j.val := hij
      omega
    · -- h1 : ¬ j.val = 0, h2 : i.val = 0
      -- Goal: 0 ≤ n
      exact Nat.zero_le _
    · -- h1 : ¬ j.val = 0, h2 : ¬ i.val = 0
      exact le_refl 0

/-!
### Helper lemmas for Proposition prop.sf.ehp-through-m

These lemmas express the elementary, complete homogeneous, and power sum symmetric
polynomials in terms of products over all variables with appropriate exponents.
-/

/-- The indicator tuple for a set S. -/
def indicatorTuple (S : Finset (Fin N)) : Fin N → ℕ := fun j => if j ∈ S then 1 else 0

/-- The single tuple with n at position i. -/
def singleTuple (i : Fin N) (n : ℕ) : Fin N → ℕ := fun j => if j = i then n else 0

/-- The count tuple for a Sym element. -/
def countTuple {n : ℕ} (s : Sym (Fin N) n) : Fin N → ℕ := fun i => Multiset.count i s.1

/-- The inverse map for indicator tuples: the support of a 0-1 tuple. -/
def indicatorSupport (a : Fin N → ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => a i = 1)

/-- The set of N-partitions of a given size, as a finite set.
    This is finite because each entry is bounded by the size. -/
def NPartitionsOfSize (n : ℕ) : Finset (NPartition N) :=
  (Fintype.piFinset (fun _ => Finset.range (n + 1))).image
    (fun f => sortTuple f) |>.filter (fun mu => mu.size = n)

end SymmetricFunctions
end AlgebraicCombinatorics
