/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.SchurBasics.Part11
import Def.Combinatorics.Young.PieriJacobiTrudi.Part32
import Lemma.Partition.NPartition
import Theorem.Combinatorics.Young.SSYTEquiv.Part3
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

/-- The equivalence between the two SSYT types. -/
def ssytEquiv (lam : SymmetricFunctions.NPartition N) :
    SymmetricFunctions.SSYT lam ≃ SSYT (sfNPartition_to_SchurBasics lam) where
  toFun := toSchurBasicsSSYT
  invFun := toSFSSYT
  left_inv := toSFSSYT_toSchurBasicsSSYT
  right_inv := toSchurBasicsSSYT_toSFSSYT

/-! ## Skew SSYT Conversions

Similar conversions for skew semistandard Young tableaux.
-/


/-- Convert a SymmetricFunctions.SkewPartition to a SchurBasics-style skew partition
    (as a pair of NPartitions). -/
def sfSkewPartition_to_SchurBasics (s : SymmetricFunctions.SkewPartition N) :
    NPartition N × NPartition N :=
  (sfNPartition_to_SchurBasics s.outer, sfNPartition_to_SchurBasics s.inner)

/-- Convert from SymmetricFunctions.SkewSSYT to SchurBasics.SkewSSYT. -/
def toSchurBasicsSkewSSYT {s : SymmetricFunctions.SkewPartition N}
    (T : SymmetricFunctions.SkewSSYT s) :
    SkewSSYT (sfSkewPartition_to_SchurBasics s).1 (sfSkewPartition_to_SchurBasics s).2 where
  entry := fun c =>
    if h : s.inner.parts c.1 ≤ c.2 ∧ c.2 < s.outer.parts c.1 then
      T.entries c.1 ⟨c.2 - s.inner.parts c.1, by omega⟩
    else
      0
  support := fun c hc => by
    rw [mem_skewYoungDiagram] at hc
    simp only [sfSkewPartition_to_SchurBasics, sfNPartition_to_SchurBasics_parts] at hc
    push Not at hc
    by_cases h1 : s.inner.parts c.1 ≤ c.2
    · have h2 := hc h1
      simp only [h1, Nat.not_lt.mpr h2, and_false, ↓reduceDIte]
    · simp only [h1, false_and, ↓reduceDIte]
  row_weak := fun i j₁ j₂ hj₁ hj₂ hlt => by
    rw [mem_skewYoungDiagram] at hj₁ hj₂
    simp only [sfSkewPartition_to_SchurBasics, sfNPartition_to_SchurBasics_parts] at hj₁ hj₂
    have hcond₁ : s.inner.parts i ≤ j₁ ∧ j₁ < s.outer.parts i := hj₁
    have hcond₂ : s.inner.parts i ≤ j₂ ∧ j₂ < s.outer.parts i := hj₂
    simp only [hcond₁, hcond₂, and_self, ↓reduceDIte]
    have hk₁_lt : j₁ - s.inner.parts i < s.outer.parts i - s.inner.parts i := by omega
    have hk₂_lt : j₂ - s.inner.parts i < s.outer.parts i - s.inner.parts i := by omega
    have hjk : (⟨j₁ - s.inner.parts i, hk₁_lt⟩ : Fin _) ≤ ⟨j₂ - s.inner.parts i, hk₂_lt⟩ := by
      simp only [Fin.le_def]; omega
    exact T.rowWeak i ⟨j₁ - s.inner.parts i, hk₁_lt⟩ ⟨j₂ - s.inner.parts i, hk₂_lt⟩ hjk
  col_strict := fun i₁ i₂ j hj₁ hj₂ hi => by
    rw [mem_skewYoungDiagram] at hj₁ hj₂
    simp only [sfSkewPartition_to_SchurBasics, sfNPartition_to_SchurBasics_parts] at hj₁ hj₂
    have hcond₁ : s.inner.parts i₁ ≤ j ∧ j < s.outer.parts i₁ := hj₁
    have hcond₂ : s.inner.parts i₂ ≤ j ∧ j < s.outer.parts i₂ := hj₂
    simp only [hcond₁, hcond₂, and_self, ↓reduceDIte]
    have hk₁_lt : j - s.inner.parts i₁ < s.outer.parts i₁ - s.inner.parts i₁ := by omega
    have hk₂_lt : j - s.inner.parts i₂ < s.outer.parts i₂ - s.inner.parts i₂ := by omega
    -- Need to show T.entries i₁ k₁ < T.entries i₂ k₂
    -- where k₁ = j - s.inner.parts i₁ and k₂ = j - s.inner.parts i₂
    -- The column condition: s.inner.parts i₁ + k₁ = s.inner.parts i₂ + k₂ = j
    have hcol_eq : s.inner.parts i₁ + (j - s.inner.parts i₁) =
                   s.inner.parts i₂ + (j - s.inner.parts i₂) := by omega
    exact T.colStrict_nonadjacent i₁ i₂ hi ⟨j - s.inner.parts i₁, hk₁_lt⟩
      ⟨j - s.inner.parts i₂, hk₂_lt⟩ hcol_eq

/-! ## Schur Polynomial Equivalences

The following theorems establish that the different Schur polynomial definitions
are equivalent.

**Summary of definitions**:
- `SchurBasics.schurPoly`: Takes `NPartition N` with `[NeZero N]`, coefficient ring `ℤ`
- `SymmetricFunctions.schur`: Takes `SymmetricFunctions.NPartition N`, generic coefficient ring `R`

The key insight is that both definitions sum over the same mathematical objects (SSYT),
just represented differently. The `ssytEquiv` equivalence provides the bijection on tableaux,
and we show that monomials are preserved under this bijection.
-/

/-- Convert a SymmetricFunctions.SSYT to a Filling for SchurBasics.schurPoly. -/
def sfSSYT_to_Filling {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) : Filling (sfNPartition_to_SchurBasics lam) :=
  fun c => T.entries c.val.1 ⟨c.val.2, by
    have hc := c.prop
    rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc
    exact hc⟩

/-- Convert a Filling (satisfying SSYT conditions) to a SymmetricFunctions.SSYT. -/
def filling_to_sfSSYT {lam : SymmetricFunctions.NPartition N}
    (f : Filling (sfNPartition_to_SchurBasics lam))
    (hf : isSSYTFillingYoung (sfNPartition_to_SchurBasics lam) f) :
    SymmetricFunctions.SSYT lam where
  entries := fun i j => f ⟨(i, j.val), by
    simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
    exact j.isLt⟩
  rowWeak := fun i j k hjk => by
    have hj_mem : (i, j.val) ∈ (sfNPartition_to_SchurBasics lam).youngDiagram := by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact Nat.lt_of_le_of_lt hjk k.isLt
    have hk_mem : (i, k.val) ∈ (sfNPartition_to_SchurBasics lam).youngDiagram := by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact k.isLt
    rcases Nat.lt_or_eq_of_le hjk with hlt | heq
    · exact hf.1 ⟨(i, j.val), hj_mem⟩ ⟨(i, k.val), hk_mem⟩ rfl hlt
    · have hj_eq_k : j = k := Fin.ext heq
      rw [hj_eq_k]
  colStrict := fun i hi j hj => by
    have hj_lt : j.val < lam.parts ⟨i.val + 1, hi⟩ := hj
    have hj_i : j.val < lam.parts i := Nat.lt_of_lt_of_le hj_lt (lam.weaklyDecreasing i ⟨i.val + 1, hi⟩ (by simp [Fin.le_def]))
    have hc1 : ((i, j.val) : Fin N × ℕ) ∈ (sfNPartition_to_SchurBasics lam).youngDiagram := by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact hj_i
    have hc2 : ((⟨i.val + 1, hi⟩, j.val) : Fin N × ℕ) ∈ (sfNPartition_to_SchurBasics lam).youngDiagram := by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact hj_lt
    exact hf.2 ⟨(i, j.val), hc1⟩ ⟨(⟨i.val + 1, hi⟩, j.val), hc2⟩ rfl (by simp [Fin.lt_def])

end SSYTEquiv
end
