/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.Partition.NPartition.Part4
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

/-- `NPartition N` forms an `AddCommMonoid` under component-wise addition.
    This enables using generic Mathlib lemmas about `AddCommMonoid` with `NPartition`. -/
instance : AddCommMonoid (NPartition N) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  nsmul := nsmulRec

/-! ## Coercion to function -/


/-- Coercion to a function. -/
instance : CoeFun (NPartition N) (fun _ => Fin N → ℕ) := ⟨parts⟩

/-! ## Partial order (containment) -/


/-- Containment of partitions: μ ≤ ν means μᵢ ≤ νᵢ for all i -/
instance instLE : LE (NPartition N) where
  le μ ν := ∀ i, μ.parts i ≤ ν.parts i

instance instPreorder : Preorder (NPartition N) where
  le := (· ≤ ·)
  le_refl := fun μ i => le_refl (μ.parts i)
  le_trans := fun μ ν ρ hab hbc i => le_trans (hab i) (hbc i)

instance instPartialOrder : PartialOrder (NPartition N) where
  le_antisymm := fun _ _ hab hba => ext (funext fun i => le_antisymm (hab i) (hba i))

/-! ## Fintype instances for bounded partitions -/


/-- The set of N-partitions with entries bounded by M is finite.
    This is useful for cardinality arguments in symmetric function theory. -/
noncomputable instance instFintypeBounded (M : ℕ) :
    Fintype { μ : NPartition N // ∀ i, μ.parts i ≤ M } := by
  -- Strategy: embed into Fin N → Fin (M + 1) which is finite
  let S := { f : Fin N → Fin (M + 1) // Antitone f }
  have hS : Fintype S := Subtype.fintype _
  let φ : { μ : NPartition N // ∀ i, μ.parts i ≤ M } → S := fun ⟨μ, hμ⟩ =>
    ⟨fun i => ⟨μ.parts i, Nat.lt_succ_of_le (hμ i)⟩, fun i j hij =>
      Fin.mk_le_mk.mpr (μ.antitone hij)⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩ heq
    apply Subtype.ext
    apply ext
    funext i
    exact Fin.val_eq_of_eq (congr_fun (congr_arg Subtype.val heq) i)
  exact Fintype.ofInjective φ hφ

/-- The set of N-partitions with size bounded by n is finite.
    This follows from the fact that if size ≤ n, then all entries are ≤ n.
    This is needed for counting SSYT of bounded content. -/
noncomputable instance instFintypeSizeBounded (n : ℕ) :
    Fintype { μ : NPartition N // μ.size ≤ n } := by
  -- If size ≤ n, then all entries are ≤ n (since each entry ≤ size)
  -- So we can embed into the bounded-entry type
  let T := { μ : NPartition N // ∀ i, μ.parts i ≤ n }
  have hT : Fintype T := instFintypeBounded n
  let φ : { μ : NPartition N // μ.size ≤ n } → T := fun ⟨μ, hμ⟩ =>
    ⟨μ, fun i => le_trans (parts_le_size μ i) hμ⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, _⟩ ⟨μ₂, _⟩ heq
    apply Subtype.ext
    exact Subtype.mk.inj (by simpa [φ] using heq)
  exact Fintype.ofInjective φ hφ

/-- The set of N-partitions with exact size n is finite.
    This is a subtype of the bounded-size type. -/
noncomputable instance instFintypeSizeEq (n : ℕ) :
    Fintype { μ : NPartition N // μ.size = n } := by
  have hBounded : Fintype { μ : NPartition N // μ.size ≤ n } := instFintypeSizeBounded n
  let φ : { μ : NPartition N // μ.size = n } → { μ : NPartition N // μ.size ≤ n } :=
    fun ⟨μ, hμ⟩ => ⟨μ, le_of_eq hμ⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, _⟩ ⟨μ₂, _⟩ heq
    apply Subtype.ext
    simpa [φ] using heq
  exact Fintype.ofInjective φ hφ

end NPartition
