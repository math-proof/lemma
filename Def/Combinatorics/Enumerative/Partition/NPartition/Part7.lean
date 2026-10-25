/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.Partition.NPartition.Part6
open Finset BigOperators

variable {N : ℕ}
/-!
# N-Partitions

This file provides the canonical definition of `NPartition N`, which represents
a weakly decreasing N-tuple of nonnegative integers (Definition def.sf.Npar in the source).

## Main definitions

* `IsNPartition` - predicate for N-tuples that are weakly decreasing
* `NPartition N` - a weakly decreasing N-tuple of nonnegative integers
* `NPartition.parts` - the entries of the partition as a function `Fin N → ℕ`
* `NPartition.antitone` - proof that the entries are weakly decreasing
* `NPartition.size` - the sum of all entries
* `NPartition.zero` - the zero partition (0, 0, ..., 0)
* `NPartition.add` - component-wise addition of N-partitions
* `NPartition.youngDiagram` - the Young diagram Y(λ) as a `Finset (Fin N × ℕ)`
* `NPartition.skewYoungDiagram` - the skew Young diagram Y(λ/μ) as a `Finset (Fin N × ℕ)`
* `NPartition.instFintypeBounded` - `Fintype` instance for partitions with bounded entries
* `NPartition.instFintypeSizeBounded` - `Fintype` instance for partitions with bounded size

## Design notes

This file provides the canonical `NPartition` structure. We use `antitone` as the
field name since it matches Mathlib conventions.

The weakly decreasing condition means: if `i ≤ j` then `parts j ≤ parts i`.
This is equivalent to `Antitone parts` in Mathlib terminology.

## Duplicate definitions

For historical reasons, there is a local `NPartition` definition in:

1. `PieriJacobiTrudi.lean` (`SymmetricFunctions.NPartition`):
   Uses `weaklyDecreasing` field name.

Both definitions are semantically equivalent (representing weakly decreasing
N-tuples of natural numbers). The local definition is retained to avoid large
refactoring of the extensive APIs built on top of it. Future work may consolidate
these definitions.

**Note**: `MonomialSymmetric.lean` and `SchurBasics.lean` have been migrated to use
the canonical definition via `abbrev` or direct import.

## Compatibility

For backwards compatibility with code using other field names:
- `NPartition.monotone` is an alias for `NPartition.antitone`
- `NPartition.weaklyDecreasing` is an alias for `NPartition.antitone`

## Migration Guide

The `NPartition` structure is defined in this file (canonical) and has one remaining
local definition:

| File                     | Namespace                       | Field name        | Status           |
|--------------------------|--------------------------------|-------------------|------------------|
| `NPartition.lean` (this) | (top-level)                    | `antitone`        | **Canonical**    |
| `PieriJacobiTrudi.lean`  | `SymmetricFunctions`           | `weaklyDecreasing`| Local (with bridge) |
| `MonomialSymmetric.lean` | `AlgebraicCombinatorics.SymmetricFunctions`   | (abbrev)          | ✓ Migrated       |
| `SchurBasics.lean`       | (top-level)                    | (import)          | ✓ Migrated       |

To migrate a file to use this shared definition:

1. Add `import AlgebraicCombinatorics.SymmetricFunctions.NPartition` to imports
2. Remove the local `structure NPartition` definition
3. If in a namespace, use `open NPartition` or create a local alias
4. Replace field accesses:
   - `.monotone` → `.antitone` or use the `monotone` alias theorem
   - `.weaklyDecreasing` → `.antitone` or use the `weaklyDecreasing` alias theorem
5. For constructors, use `NPartition.mk` with `antitone` field, or use `NPartition.mk'`
   which accepts the explicit predicate form

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/MonomialSymmetric.tex (Definition def.sf.Npar)
-/


namespace NPartition

variable {N : ℕ}

/-- Convert a partition (as a `Nat.Partition`) to an N-partition by padding with zeros.
    Requires that the partition has at most N parts.

    This corresponds to the map in Proposition prop.sf.Npar-as-par:
    (μ₁, μ₂, ..., μ_ℓ) ↦ (μ₁, μ₂, ..., μ_ℓ, 0, 0, ..., 0) -/
def ofPartition {n : ℕ} (p : Nat.Partition n) (_hp : Multiset.card p.parts ≤ N) : NPartition N where
  parts := fun i =>
    let sorted := p.parts.sort (· ≥ ·)
    if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0
  antitone := by
    intro i j hij
    simp only
    split_ifs with hi hj hj
    · -- Both in range: use that sorted list is decreasing
      have hsorted : (p.parts.sort (· ≥ ·)).Pairwise (· ≥ ·) :=
        Multiset.pairwise_sort (r := (· ≥ ·)) p.parts
      exact List.Pairwise.rel_get_of_le hsorted hij
    · -- i in range, j out of range: contradiction since i ≤ j
      omega
    · -- i out of range: 0 ≤ anything
      exact Nat.zero_le _
    · -- both out of range
      exact le_refl 0

/-- Convert an N-partition to a partition by removing trailing zeros. -/
def toPartition (μ : NPartition N) : Nat.Partition μ.size where
  parts := (Finset.univ.val.map μ.parts).filter (· ≠ 0)
  parts_pos := by
    intro i hi
    simp only [Multiset.mem_filter, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at hi
    omega
  parts_sum := by
    simp only [size]
    have h : (Finset.univ.val.map μ.parts).sum = ∑ i, μ.parts i := by
      simp [Finset.sum_eq_multiset_sum]
    rw [← h]
    exact filter_ne_zero_sum _

/-! ## Young Diagram (Definition def.sf.ydiag)

The Young diagram Y(λ) of an N-partition λ is the set of cells (i, j) where
i ∈ [N] and j ∈ [λ_i].

Note: Mathlib has `YoungDiagram` which is more general (infinite diagrams).
Here we define a version specific to N-partitions. -/


/-- The Young diagram Y(λ) of an N-partition λ is the set of cells (i, j) where
    i ∈ Fin N and j < λ_i.
    Definition def.sf.ydiag in the source.

    Note: Mathlib has `YoungDiagram` which is more general (infinite diagrams).
    Here we define a version specific to N-partitions. -/
def youngDiagram (μ : NPartition N) : Finset (Fin N × ℕ) :=
  Finset.univ.biUnion fun i => (Finset.range (μ.parts i)).map
    ⟨fun j => (i, j), fun _ _ h => congr_arg Prod.snd h⟩

end NPartition
