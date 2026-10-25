/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.SchurBasics.Part11
import Def.Combinatorics.Young.PieriJacobiTrudi.Part32
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.SSYTEquiv.Part3
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

omit [NeZero N] in
/-- Two SSYTs in the SymmetricFunctions namespace are equal if their entries are equal. -/
theorem SSYT_eq_of_entries_eq {lam : SymmetricFunctions.NPartition N}
    {T1 T2 : SymmetricFunctions.SSYT lam}
    (h : T1.entries = T2.entries) : T1 = T2 := by
  cases T1; cases T2
  simp only at h
  subst h
  rfl

/-- The conversions are inverses (direction 1). -/
theorem toSFSSYT_toSchurBasicsSSYT {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    toSFSSYT (toSchurBasicsSSYT T) = T := by
  apply SSYT_eq_of_entries_eq
  funext i j
  simp only [toSFSSYT, toSchurBasicsSSYT]
  have hj_lt : j.val < lam.parts i := j.isLt
  simp only [hj_lt, ↓reduceDIte]
  rfl

/-- The conversions are inverses (direction 2). -/
theorem toSchurBasicsSSYT_toSFSSYT {lam : NPartition N}
    (T : SSYT lam) :
    toSchurBasicsSSYT (toSFSSYT T) = T := by
  apply SSYT.ext
  intro c
  simp only [toSchurBasicsSSYT, toSFSSYT]
  by_cases h : c.2 < lam.parts c.1
  · simp only [schurBasicsNPartition_to_SF_parts, h, ↓reduceDIte]
  · simp only [schurBasicsNPartition_to_SF_parts, h, ↓reduceDIte]
    have hc : c ∉ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram]
      exact h
    exact (T.toYoungTableau.support c hc).symm

end SSYTEquiv
end
