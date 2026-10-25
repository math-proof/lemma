/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Theorem.Combinatorics.Young.MonomialSymmetric
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
## N-partitions (Definition def.sf.Npar)

An N-partition is a weakly decreasing N-tuple of nonnegative integers.

This namespace uses the canonical `NPartition` definition from `NPartition.lean`
(imported above). All basic lemmas (`ext`, `size`, `zero`, `length`, etc.) are
inherited from the canonical definition via the `abbrev` below.
-/


/-- Alias for the canonical `NPartition` type within this namespace.
    An N-partition is a weakly decreasing N-tuple of nonnegative integers.
    (Definition def.sf.Npar)

    This is represented as a function `Fin N → ℕ` that is antitone
    (i.e., `i ≤ j → parts j ≤ parts i`).

    All basic operations (`size`, `length`, `zero`, etc.) and lemmas are inherited
    from the canonical `_root_.NPartition` definition in `NPartition.lean`. -/
abbrev NPartition (N : ℕ) := _root_.NPartition N

namespace NPartition

/-!
## Bijection with partitions of length ≤ N (Proposition prop.sf.Npar-as-par)

There is a bijection between partitions of length ≤ N and N-partitions.

The core definitions (`ofPartition`, `toPartition`, `ofPartition_size`, `toPartition_card_le`)
are defined in `NPartition.lean` and re-exported here for convenience within this namespace.
-/

-- All basic definitions and lemmas (ext, DecidableEq, size, zero, length, etc.)
-- are inherited from _root_.NPartition in NPartition.lean.


-- Re-export canonical definitions from _root_.NPartition to this namespace.
-- This allows code in this file to use `ofPartition`, `toPartition`, etc.
-- without qualification, while avoiding code duplication.

/-- Convert a partition (as a `Nat.Partition`) to an N-partition by padding with zeros.
    Re-export of `_root_.NPartition.ofPartition`. -/
abbrev ofPartition {n : ℕ} (p : Nat.Partition n) (hp : Multiset.card p.parts ≤ N) : NPartition N :=
  _root_.NPartition.ofPartition p hp

/-- Convert an N-partition to a partition by removing trailing zeros.
    Re-export of `_root_.NPartition.toPartition`. -/
abbrev toPartition (mu : NPartition N) : Nat.Partition mu.size :=
  _root_.NPartition.toPartition mu

end NPartition
end SymmetricFunctions
end AlgebraicCombinatorics
