/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.SchurBasics.Part11
import Def.Combinatorics.Young.PieriJacobiTrudi.Part32
import Lemma.Partition.NPartition
import Theorem.Combinatorics.Young.SSYTEquiv.Part2
/-!
# Equivalence Between SSYT Definitions

This file establishes the equivalence between the two definitions of semistandard
Young tableaux (SSYT) in this project:

1. **SchurBasics.SSYT**: Uses `entry : Fin N × ℕ → Fin N` with a support condition
   that entries outside the Young diagram are 0. This representation is more
   flexible for proofs involving cell coordinates.

2. **SymmetricFunctions.SSYT**: Uses dependent types `entries : (i : Fin N) →
   (j : Fin (lam.parts i)) → Fin N`. This representation is more type-safe but
   harder to work with for some proofs.

## Main Results

* `npartitionEquiv`: An equivalence between the two NPartition types
* `ssytEquiv`: An equivalence between the two SSYT types
* `toSchurBasicsSSYT`: Convert from SymmetricFunctions.SSYT to SchurBasics.SSYT
* `toSFSSYT`: Convert from SchurBasics.SSYT to SymmetricFunctions.SSYT
* `schur_eq_schurPoly_int`: Equivalence of Schur polynomial definitions
* `schurPoly_eq_schur`: Corollary for composing theorems from different files

## Implementation Notes

The two definitions also use different `NPartition` types (with fields `monotone`
vs `weaklyDecreasing`), so we also provide conversions between these.

The SkewSSYT definitions have a similar relationship and are also addressed here.

## Schur Polynomial Equivalence

The project has three Schur polynomial definitions:
- `SchurBasics.schurPoly`: Takes `NPartition N` with `[NeZero N]`, coefficient ring `ℤ`
- `SymmetricFunctions.schur`: Takes `SymmetricFunctions.NPartition N`, generic ring `R`
- `AlgebraicCombinatorics.schurPoly`: Takes `Fin N → ℕ` with `IsNPartition`, generic ring `R`

This file provides equivalence theorems between the first two definitions.
The third definition (in LittlewoodRichardson.lean) is related via the `IsNPartition`
predicate, which is equivalent to the bundled `NPartition` types.

## Design Rationale

Both SSYT definitions are retained in their original files. This file provides the
equivalence infrastructure for code that needs both representations.

The two representations serve different purposes:
- `SchurBasics.SSYT`: Better for proofs using cell coordinates, extends `YoungTableau`
- `SymmetricFunctions.SSYT`: Better for type-safe code, no `[NeZero N]` requirement

## NPartition Types

This file bridges between the two `NPartition` types in this project:
- `NPartition N` (shared, from NPartition.lean) - uses `antitone` field
- `SymmetricFunctions.NPartition N` (local, from PieriJacobiTrudi.lean) - uses
  `weaklyDecreasing` field

Both equivalences are provided for API convenience:
- `SSYTEquiv.npartitionEquiv`: shared → local
- `SymmetricFunctions.NPartition.equivShared`: local → shared

## Tags

semistandard Young tableau, SSYT, equivalence, Young diagram, Schur polynomial
-/


noncomputable section

open Finset BigOperators MvPolynomial

namespace SSYTEquiv

variable {N : ℕ} [NeZero N]

/-- Convert from SymmetricFunctions.SSYT to SchurBasics.SSYT.

The key insight is that the dependent type `(j : Fin (lam.parts i))` in the SF
definition corresponds to cells `(i, j)` where `j < lam.parts i`, which is exactly
the membership condition for the Young diagram in SchurBasics. -/
def toSchurBasicsSSYT {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) : SSYT (sfNPartition_to_SchurBasics lam) where
  entry := fun c =>
    if h : c.2 < lam.parts c.1 then
      T.entries c.1 ⟨c.2, h⟩
    else
      0
  support := fun c hc => by
    rw [NPartition.mem_youngDiagram] at hc
    simp only [sfNPartition_to_SchurBasics_parts] at hc
    simp [hc]
  row_weak := fun i j₁ j₂ hj₂ hlt => by
    rw [NPartition.mem_youngDiagram] at hj₂
    simp only [sfNPartition_to_SchurBasics_parts] at hj₂
    have hj₁ : j₁ < lam.parts i := Nat.lt_of_lt_of_le hlt (Nat.le_of_lt hj₂)
    simp only [hj₁, hj₂, ↓reduceDIte]
    exact T.rowWeak i ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ (Nat.le_of_lt hlt)
  col_strict := fun i₁ i₂ j hj₂ hi => by
    rw [NPartition.mem_youngDiagram] at hj₂
    simp only [sfNPartition_to_SchurBasics_parts] at hj₂
    have hj₁ : j < lam.parts i₁ := by
      calc j < lam.parts i₂ := hj₂
        _ ≤ lam.parts i₁ := lam.weaklyDecreasing i₁ i₂ (Nat.le_of_lt hi)
    simp only [hj₁, hj₂, ↓reduceDIte]
    exact sf_ssyt_col_strict_nonadjacent T hj₁ hj₂ hi

/-- Convert from SchurBasics.SSYT to SymmetricFunctions.SSYT.

This requires extracting the entries at valid positions from the total function. -/
def toSFSSYT {lam : NPartition N}
    (T : SSYT lam) : SymmetricFunctions.SSYT (schurBasicsNPartition_to_SF lam) where
  entries := fun i j => T.entry (i, j.val)
  rowWeak := fun i j k hjk => by
    have hk : (i, k.val) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram]
      exact k.isLt
    have hj_lt : j.val < k.val ∨ j.val = k.val := Nat.lt_or_eq_of_le hjk
    rcases hj_lt with hlt | heq
    · exact T.row_weak i j.val k.val hk hlt
    · rw [heq]
  colStrict := fun i hi j hj => by
    simp only [schurBasicsNPartition_to_SF_parts] at hj
    have hmem : (⟨i.val + 1, hi⟩, j.val) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram]
      exact hj
    have hlt : i < ⟨i.val + 1, hi⟩ := by simp only [Fin.lt_def]; omega
    exact T.col_strict i ⟨i.val + 1, hi⟩ j.val hmem hlt

end SSYTEquiv
end
