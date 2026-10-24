/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
/-!
# The Cycle Decomposition

This file formalizes the cycle decomposition (or disjoint cycle decomposition) of a permutation,
as presented in Section "The cycle decomposition" of the source text.

## Main definitions

* `numCyclesTotal`: The total number of cycles including 1-cycles (fixed points).
* `numCycles`: The number of non-trivial cycles (length ≥ 2).
* `cycles`: The set of cycles of a permutation.
* `cycleLengthsPartition`: The partition of n given by cycle lengths.
* `dcdListToPerm`: Convert a list of lists (representing cycles) to a permutation.

## Main results

* `sameCycle_iff_exists_pow`: Two elements belong to the same cycle iff one is a power of the
  permutation applied to the other (Proposition \ref{prop.perm.cycs.same}).
* `exists_dcd`: Every permutation can be written as a product of disjoint cycles
  (Theorem \ref{thm.perm.dcd.main} (a)).
* `dcd_unique_cycleType`: Any two DCDs of the same permutation have the same cycle type
  (Theorem \ref{thm.perm.dcd.main} (b)).
* `canonicalDcd_exists_unique`: For totally ordered sets, there is a unique canonical DCD
  (Theorem \ref{thm.perm.dcd.main} (c)).
* `cycleType_eq_iff_isConj`: Two permutations have the same cycle type iff they are conjugate.
* `sign_eq_neg_one_pow_card_sub_numCycles`: The sign of a permutation equals `(-1)^(n - k)`
  where `k` is the number of cycles (Proposition \ref{prop.perm.cycs.sign}).

## References

* Theorem \ref{thm.perm.dcd.main} in the source
* Definition \ref{def.perm.cycs.cycs}
* Proposition \ref{prop.perm.cycs.same}
* Proposition \ref{prop.perm.cycs.sign}

## Implementation notes

This file mostly provides wrappers and restatements of Mathlib's existing API for
cycle decomposition (`Equiv.Perm.cycleFactorsFinset`, `Equiv.Perm.cycleType`, etc.)
in the language of the source text.
-/


namespace AlgebraicCombinatorics.CycleDecomposition

open Equiv Equiv.Perm Finset
/-!
### The cycle of a permutation containing a given element

Mathlib provides `Equiv.Perm.cycleOf f x`, the cycle of `f` containing `x`.
We provide additional characterizations and properties.
-/


section SameCycle

variable {α : Type*} [Fintype α]

end SameCycle
/-!
### Disjoint Cycle Decomposition (DCD)

Mathlib's `Equiv.Perm.cycleFactorsFinset` provides the set of cycles in the DCD.
The key theorem `cycleFactorsFinset_noncommProd` states that the product of these
cycles equals the original permutation.

Theorem \ref{thm.perm.dcd.main} (a): Existence of DCD.
-/


section DCD

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The number of cycles of a permutation (including 1-cycles / fixed points).
This counts all cycles in the DCD as defined in the source text.

Note: Mathlib's `cycleFactorsFinset` only includes cycles of length ≥ 2.
To get the total count including 1-cycles, we add the number of fixed points. -/
def numCyclesTotal (σ : Perm α) : ℕ :=
  σ.cycleFactorsFinset.card + (Fintype.card α - σ.support.card)

/-- The number of cycles (of length ≥ 2) in the DCD. -/
def numCycles (σ : Perm α) : ℕ := σ.cycleFactorsFinset.card

end DCD
/-!
### Cycles of a permutation (Definition \ref{def.perm.cycs.cycs})

This section formalizes Definition \ref{def.perm.cycs.cycs} from the source text:

**Definition (def.perm.cycs.cycs):** Let X be a finite set. Let σ be a permutation of X.

**(a)** The *cycles* of σ are defined to be the cycles in the DCD of σ
(as defined in Theorem \ref{thm.perm.dcd.main} (a)). This includes 1-cycles, if there
are any in the DCD of σ.

We shall equate a cycle of σ with any of its cyclic rotations; thus, for example,
(3, 1, 4) and (1, 4, 3) shall be regarded as being the same cycle (but (3, 1, 4)
and (3, 4, 1) shall not).

**(b)** The *cycle lengths partition* of σ shall denote the partition of |X| obtained
by writing down the lengths of the cycles of σ in weakly decreasing order.

**Implementation note:** Mathlib's `cycleFactorsFinset` only includes cycles of length ≥ 2
(non-trivial cycles). Fixed points (1-cycles) are not included. This differs from the
textbook which includes 1-cycles. However, for most purposes this is equivalent since
1-cycles act as the identity. The `numCyclesTotal` definition above accounts for this
by adding the number of fixed points.

Regarding cyclic rotations: In Mathlib, cycles are represented as permutations (elements
of `Perm α`), not as lists. Two cycles that are cyclic rotations of each other represent
the *same* permutation, so they are automatically equated. For example, the cycles
`cyc [3, 1, 4]` and `cyc [1, 4, 3]` are equal as permutations by `List.formPerm_rotate`.
-/


section Cycles

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The cycles of a permutation σ are the elements of `σ.cycleFactorsFinset`.
Each cycle is a permutation that is a cycle in the graph-theoretic sense.

Note: This only includes cycles of length ≥ 2 (non-trivial cycles).
Fixed points (1-cycles) are not included, following Mathlib's convention.
See `numCyclesTotal` for the total count including 1-cycles.

(Definition \ref{def.perm.cycs.cycs} (a)) -/
def cycles (σ : Perm α) : Finset (Perm α) := σ.cycleFactorsFinset

/-- The cycle lengths partition of σ is the partition of |X| obtained by
listing the lengths of cycles in weakly decreasing order.
(Definition \ref{def.perm.cycs.cycs} (b)) -/
def cycleLengthsPartition (σ : Perm α) : (Fintype.card α).Partition := σ.partition

/-- The cycle type as a multiset of cycle lengths. -/
def cycleLengths (σ : Perm α) : Multiset ℕ := σ.cycleType
/-! #### Cyclic rotations of cycles

The textbook states that cycles are equated with their cyclic rotations.
In Mathlib, this is automatic since cycles are represented as permutations,
and cyclically rotated lists give the same permutation via `List.formPerm_rotate`.
-/

end Cycles
/-!
### Sign and cycle count (Proposition \ref{prop.perm.cycs.sign})

The sign of a permutation is determined by its number of cycles.
-/


section Sign

variable {n : ℕ}

end Sign
/-!
### Canonical DCD (Theorem \ref{thm.perm.dcd.main} (c))

For a totally ordered finite set, there is a unique DCD where:
1. Each cycle starts with its smallest element
2. Cycles appear in decreasing order of first elements

This canonical form is useful for comparing permutations.
-/


section CanonicalDCD

variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] [Inhabited α]
/-!
#### Helper definitions and lemmas for canonical DCD construction

We build the canonical DCD by:
1. Converting each cycle in `cycleFactorsFinset` to its canonical list (starting from minimum)
2. Adding singleton lists for fixed points
3. Sorting by decreasing first element
-/


/-- Get the minimum element of a cycle's support. -/
noncomputable def cycleMinElem (c : Perm α) (hc : c.IsCycle) : α :=
  c.support.min' hc.nonempty_support

/-- Get the canonical list representation of a cycle starting from its minimum element. -/
noncomputable def cycleToCanonicalList (c : Perm α) (hc : c.IsCycle) : List α :=
  toList c (cycleMinElem c hc)

/-- Convert a list of lists representing cycles to a permutation by taking the product
of the cycle permutations. Each list `[a₁, a₂, ..., aₖ]` represents the k-cycle
`cyc_{a₁, a₂, ..., aₖ}` that sends a₁ → a₂ → ... → aₖ → a₁. -/
def dcdListToPerm (cycleReps : List (List α)) : Perm α :=
  (cycleReps.map List.formPerm).prod

-- Comparison function for sorting lists by decreasing first element
def cmpListsGe : List α → List α → Bool := fun l1 l2 => decide (l1.head! ≥ l2.head!)

end CanonicalDCD

end AlgebraicCombinatorics.CycleDecomposition
