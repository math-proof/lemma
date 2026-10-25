/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.SchurBasics.Part11
import Def.Combinatorics.Young.PieriJacobiTrudi.Part32
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.SSYTEquiv.Part2
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
/-- Helper lemma: column-strict property extends to non-adjacent rows for SF SSYT.
    If j is in rows i₁ and i₂ with i₁ < i₂, then T.entries i₁ j < T.entries i₂ j. -/
theorem sf_ssyt_col_strict_nonadjacent {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) {i₁ i₂ : Fin N} {j : ℕ}
    (hj₁ : j < lam.parts i₁) (hj₂ : j < lam.parts i₂) (hi : i₁ < i₂) :
    T.entries i₁ ⟨j, hj₁⟩ < T.entries i₂ ⟨j, hj₂⟩ := by
  -- Use strong induction on the distance between rows
  obtain ⟨d, hd_eq⟩ : ∃ d, i₂.val - i₁.val = d + 1 := ⟨i₂.val - i₁.val - 1, by omega⟩
  induction d using Nat.strong_induction_on generalizing i₁ i₂ with
  | _ d ih =>
    by_cases hd : d = 0
    · -- Base case: adjacent rows (i₂ = i₁ + 1)
      have hi₂_eq : i₂.val = i₁.val + 1 := by omega
      have hi_lt : i₁.val + 1 < N := by omega
      have hi₂_fin : i₂ = ⟨i₁.val + 1, hi_lt⟩ := Fin.ext hi₂_eq
      subst hi₂_fin
      exact T.colStrict i₁ hi_lt ⟨j, hj₁⟩ hj₂
    · -- Inductive case: i₂.val - i₁.val > 1
      have hi₂_gt : i₂.val > i₁.val + 1 := by omega
      -- Find intermediate row i' = i₁.val + 1
      let i' : Fin N := ⟨i₁.val + 1, by omega⟩
      have hi₁_i' : i₁ < i' := by simp only [i', Fin.lt_def]; omega
      have hi'_i₂ : i' < i₂ := by simp only [i', Fin.lt_def]; omega
      -- j is in row i' too (by partition monotonicity)
      have hj' : j < lam.parts i' :=
        Nat.lt_of_lt_of_le hj₂ (lam.weaklyDecreasing i' i₂ (Nat.le_of_lt hi'_i₂))
      -- Apply T.colStrict for i₁ → i'
      have h1 : T.entries i₁ ⟨j, hj₁⟩ < T.entries i' ⟨j, hj'⟩ := by
        have hi_lt : i₁.val + 1 < N := by omega
        have hj'_alt : j < lam.parts ⟨i₁.val + 1, hi_lt⟩ := hj'
        have hcol := T.colStrict i₁ hi_lt ⟨j, hj₁⟩ hj'_alt
        convert hcol using 2
      -- Apply IH for i' → i₂
      have hdiff' : i₂.val - i'.val - 1 < d := by simp only [i']; omega
      have hdiff'_eq : i₂.val - i'.val = (i₂.val - i'.val - 1) + 1 := by omega
      have h2 : T.entries i' ⟨j, hj'⟩ < T.entries i₂ ⟨j, hj₂⟩ :=
        ih (i₂.val - i'.val - 1) hdiff' hj' hj₂ hi'_i₂ hdiff'_eq
      exact lt_trans h1 h2

end SSYTEquiv
end
