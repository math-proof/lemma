/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.SchurBasics.Part11
import Def.Combinatorics.Young.PieriJacobiTrudi.Part32
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.SSYTEquiv
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
/-- The conversions are inverses (direction 1). -/
@[simp]
theorem sfNPartition_schurBasics_id (lam : NPartition N) :
    sfNPartition_to_SchurBasics (schurBasicsNPartition_to_SF lam) = lam := by
  cases lam; rfl

omit [NeZero N] in
/-- The conversions are inverses (direction 2). -/
@[simp]
theorem schurBasics_sfNPartition_id (lam : SymmetricFunctions.NPartition N) :
    schurBasicsNPartition_to_SF (sfNPartition_to_SchurBasics lam) = lam := by
  cases lam; rfl

omit [NeZero N] in
/-- The parts are preserved by conversion. -/
@[simp]
theorem schurBasicsNPartition_to_SF_parts (lam : NPartition N) :
    (schurBasicsNPartition_to_SF lam).parts = lam.parts := rfl

omit [NeZero N] in
@[simp]
theorem sfNPartition_to_SchurBasics_parts (lam : SymmetricFunctions.NPartition N) :
    (sfNPartition_to_SchurBasics lam).parts = lam.parts := rfl

end SSYTEquiv
end
