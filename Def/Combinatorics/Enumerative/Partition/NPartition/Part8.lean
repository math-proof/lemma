/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.Combinatorics.Enumerative.Partition.NPartition.Part7
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

/-! ## Skew Young Diagram (Definition def.sf.skew-diag)

**This is the canonical `Finset` version of skew Young diagrams.**

The skew Young diagram Y(λ/μ) of two N-partitions λ and μ (where μ ⊆ λ componentwise)
is the set of cells in Y(λ) but not in Y(μ). In other words:
  Y(λ/μ) = {(i, j) | μ_i ≤ j < λ_i}

This uses 0-indexed columns (j starts from 0), following Mathlib/programming conventions.

**Alternative definitions:**
- `AlgebraicCombinatorics.skewYoungDiagram` in LittlewoodRichardson.lean returns a `Set`
  and uses 1-indexed columns: {(i, j) | μ_i < j ≤ λ_i}. This matches textbook conventions.
- `skewYoungDiagram` in SchurBasics.lean is a duplicate that requires `[NeZero N]`.
  Prefer this canonical version when possible.

The two indexing conventions are equivalent via the bijection (i, j) ↔ (i, j+1).
See `SchurBasics.skewYoungDiagram_equiv_LR` for the equivalence proof. -/


/-- The skew Young diagram Y(λ/μ) is the set difference Y(λ) \ Y(μ).
    This consists of cells (i, j) where μ_i ≤ j < λ_i.
    Definition def.sf.skew-diag in the source.

    **This is the canonical `Finset` version of skew Young diagrams.**
    
    Other versions exist for different use cases:
    - `AlgebraicCombinatorics.skewYoungDiagram` in LittlewoodRichardson.lean returns a `Set`
      and uses 1-indexed columns (textbook convention)
    - `skewYoungDiagram` in SchurBasics.lean is a duplicate that requires `[NeZero N]`
      (prefer this canonical version)

    **Indexing Convention**: Uses 0-indexed columns (Mathlib convention).
    - Here: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i
    - LittlewoodRichardson: (i, j) ∈ Y(λ/μ) iff μ_i < j ≤ λ_i (1-indexed)
    
    The bijection (i, j) ↔ (i, j+1) converts between conventions.
    See `SchurBasics.skewYoungDiagram_equiv_LR` for the equivalence proof. -/
def skewYoungDiagram (lam mu : NPartition N) : Finset (Fin N × ℕ) :=
  lam.youngDiagram \ mu.youngDiagram

end NPartition
