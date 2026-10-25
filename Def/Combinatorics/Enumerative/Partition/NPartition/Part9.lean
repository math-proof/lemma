/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.Combinatorics.Enumerative.Partition.NPartition.Part8
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

/-! ## Row and Column Partitions

Special partitions consisting of a single row or column, used in the
Pieri rules and connections to symmetric functions. These are moved from
PieriJacobiTrudi.lean as part of the consolidation effort. -/


/-- The row partition (n, 0, 0, ..., 0) with n boxes in the first row.
    This is the partition corresponding to h_n (complete homogeneous symmetric polynomial).
    Requires N > 0 to have at least one row. -/
def rowPartition (N : ℕ) (n : ℕ) (_hN : 0 < N) : NPartition N where
  parts := fun i => if i.val = 0 then n else 0
  antitone := by
    intro i j hij
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      split_ifs <;> omega
    · by_cases hj : j.val = 0
      · omega  -- i > 0 but j = 0 contradicts i ≤ j
      · simp only [hj, ↓reduceIte, hi]; rfl

/-- The column partition (1, 1, ..., 1, 0, ..., 0) with n ones (n boxes in first column).
    This is the partition corresponding to e_n (elementary symmetric polynomial).
    Requires n ≤ N (can't have more rows than N). -/
def colPartition (N : ℕ) (n : ℕ) (_hn : n ≤ N) : NPartition N where
  parts := fun i => if i.val < n then 1 else 0
  antitone := by
    intro i j hij
    simp only
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · simp [hi, hj]
      · simp [hi, hj]
    · by_cases hj : j.val < n
      · omega -- i.val >= n but j.val < n contradicts i ≤ j
      · simp [hi, hj]

/-! ## Transpose of a partition

The transpose of a partition λ is denoted λᵗ and satisfies:
(λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.

Since we work with fixed-length tuples, we define a predicate `IsTranspose`
that captures when two tuples represent transpose partitions. -/


/-- The transpose of a partition.
    See Exercise exe.pars.transpose in the source.
    The transpose λᵗ satisfies: (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.
    The length of the transpose equals the first (largest) part of λ. -/
noncomputable def transpose (μ : NPartition N) (hN : 0 < N) : NPartition (μ.parts ⟨0, hN⟩) where
  parts := fun i => (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ μ.parts j).card
  antitone := by
    intro i j hij
    apply Finset.card_le_card
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact le_trans (Nat.add_le_add_right hij 1) hr

/-- Predicate asserting that `lamt` is the transpose of `lam`.
    The transpose λᵗ of a partition λ satisfies:
    (λᵗ)ᵢ = |{j : λⱼ ≥ i}| for each i.

    Since we work with fixed-length tuples, this predicate captures
    when two tuples represent transpose partitions (possibly with trailing zeros). -/
def IsTranspose {M : ℕ} (lam : Fin N → ℕ) (lamt : Fin M → ℕ) : Prop :=
  (∀ i : Fin M, lamt i = (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ lam j).card) ∧
  (∀ j : Fin N, lam j = (Finset.univ.filter fun i : Fin M => j.val + 1 ≤ lamt i).card)

end NPartition
