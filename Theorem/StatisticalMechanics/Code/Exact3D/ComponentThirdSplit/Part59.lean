/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part61
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRows_nonneg
    {β H D : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (hDpos : 0 < D)
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R} :
    (SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H D Ω ι label).Nonneg := by
  classical
  have hB :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
      hβ hH n Ω v
  rcases hB with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, _hfourNoneBudget,
      _hfourEndpointBudget, _hfourOriginBudget, _hfourOriginEndpointBudget,
      _hfourGhostBudget, _hfourGhostEndpointBudget,
      _hfourGhostOriginBudget, _hfourGhostOriginEndpointBudget⟩
  refine
    ⟨div_nonneg hzeroNone (le_of_lt hDpos),
      div_nonneg htwoNone (le_of_lt hDpos),
      div_nonneg htwoEndpoint (le_of_lt hDpos),
      div_nonneg htwoOrigin (le_of_lt hDpos),
      div_nonneg htwoGhost (le_of_lt hDpos),
      div_nonneg htwoGhostEndpoint (le_of_lt hDpos),
      div_nonneg htwoGhostOrigin (le_of_lt hDpos), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _hk
    dsimp [SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          div_nonneg
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
              hβ hH E)
            (le_of_lt hDpos))))
  · intro k _hk
    dsimp [SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          div_nonneg
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
              hβ hH E)
            (le_of_lt hDpos))))
  · intro k _hk
    dsimp [SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          div_nonneg
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
              hβ hH E)
            (le_of_lt hDpos))))
  · intro k _hk
    dsimp [SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          div_nonneg
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
              hβ hH E)
            (le_of_lt hDpos))))
  · intro k _hk
    dsimp [SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          div_nonneg
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
              hβ hH E)
            (le_of_lt hDpos))))
  · intro k _hk
    dsimp [SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          div_nonneg
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
              hβ hH E)
            (le_of_lt hDpos))))
  · intro k _hk
    dsimp [SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          div_nonneg
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
              hβ hH E)
            (le_of_lt hDpos))))
  · intro k _hk
    dsimp [SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          div_nonneg
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
              hβ hH E)
            (le_of_lt hDpos))))

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.toBudget15_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (h : Sh.Nonneg) :
    SourceClassEndpointMembershipLiveBudget15.Nonneg Sh.toBudget15 := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun k hk => hfourNone k hk)
  · exact Finset.sum_nonneg (fun k hk => hfourEndpoint k hk)
  · exact Finset.sum_nonneg (fun k hk => hfourOrigin k hk)
  · exact Finset.sum_nonneg (fun k hk => hfourOriginEndpoint k hk)
  · exact Finset.sum_nonneg (fun k hk => hfourGhost k hk)
  · exact Finset.sum_nonneg (fun k hk => hfourGhostEndpoint k hk)
  · exact Finset.sum_nonneg (fun k hk => hfourGhostOrigin k hk)
  · exact Finset.sum_nonneg (fun k hk => hfourGhostOriginEndpoint k hk)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.ofFourShare_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {fourShare : Bool → Bool → Bool → ℕ → ℝ}
    (hzeroNone : 0 ≤ zero_none)
    (htwoNone : 0 ≤ two_none)
    (htwoEndpoint : 0 ≤ two_endpoint)
    (htwoOrigin : 0 ≤ two_origin)
    (htwoGhost : 0 ≤ two_ghost)
    (htwoGhostEndpoint : 0 ≤ two_ghost_endpoint)
    (htwoGhostOrigin : 0 ≤ two_ghost_origin)
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          0 ≤ fourShare hasGhost hasOrigin hasEndpoint k) :
    (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin fourShare).Nonneg := by
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare]
      using hfour false false false k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare]
      using hfour false false true k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare]
      using hfour false true false k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare]
      using hfour false true true k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare]
      using hfour true false false k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare]
      using hfour true false true k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare]
      using hfour true true false k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare]
      using hfour true true true k hk

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare_toBudget15_fieldwiseLe
    {n : ℕ} {v : FK.boxVerts 3 n}
    {zero_noneA two_noneA two_endpointA two_originA two_ghostA
      two_ghost_endpointA two_ghost_originA : ℝ}
    {zero_noneB two_noneB two_endpointB two_originB two_ghostB
      two_ghost_endpointB two_ghost_originB : ℝ}
    {fourA fourB : Bool → Bool → Bool → ℕ → ℝ}
    (hzeroNone : zero_noneA ≤ zero_noneB)
    (htwoNone : two_noneA ≤ two_noneB)
    (htwoEndpoint : two_endpointA ≤ two_endpointB)
    (htwoOrigin : two_originA ≤ two_originB)
    (htwoGhost : two_ghostA ≤ two_ghostB)
    (htwoGhostEndpoint : two_ghost_endpointA ≤ two_ghost_endpointB)
    (htwoGhostOrigin : two_ghost_originA ≤ two_ghost_originB)
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          fourA hasGhost hasOrigin hasEndpoint k ≤
            fourB hasGhost hasOrigin hasEndpoint k) :
    SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
      (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
        v zero_noneA two_noneA two_endpointA two_originA two_ghostA
        two_ghost_endpointA two_ghost_originA fourA).toBudget15
      (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
        v zero_noneB two_noneB two_endpointB two_originB two_ghostB
        two_ghost_endpointB two_ghost_originB fourB).toBudget15 := by
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      hzeroNone
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoNone
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoEndpoint
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoOrigin
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhost
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhostEndpoint
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhostOrigin
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum (fun k hk => hfour false false false k hk)
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum (fun k hk => hfour false false true k hk)
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum (fun k hk => hfour false true false k hk)
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum (fun k hk => hfour false true true k hk)
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum (fun k hk => hfour true false false k hk)
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum (fun k hk => hfour true false true k hk)
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum (fun k hk => hfour true true false k hk)
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum (fun k hk => hfour true true true k hk)

set_option linter.style.longLine false in

theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {fourShare : Bool → Bool → Bool → ℕ → ℝ}
    (hzeroNone : 0 ≤ zero_none)
    (htwoNone : 0 ≤ two_none)
    (htwoEndpoint : 0 ≤ two_endpoint)
    (htwoOrigin : 0 ≤ two_origin)
    (htwoGhost : 0 ≤ two_ghost)
    (htwoGhostEndpoint : 0 ≤ two_ghost_endpoint)
    (htwoGhostOrigin : 0 ≤ two_ghost_origin)
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          0 ≤ fourShare hasGhost hasOrigin hasEndpoint k) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin fourShare := by
  let Sh :=
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin fourShare
  have hSh : Sh.Nonneg := by
    simpa [Sh] using
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_nonneg
        (v := v) hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
        htwoGhostEndpoint htwoGhostOrigin hfour
  have htotal : 0 ≤ Sh.total := by
    simpa [SourceClassEndpointMembershipResidualShellShare15.total] using
      SourceClassEndpointMembershipLiveBudget15.total_nonneg
        (SourceClassEndpointMembershipResidualShellShare15.toBudget15_nonneg
          hSh)
  simpa [
    Sh,
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare_total_eq_expandedOfFourShareTotal] using
    htotal

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_mono
    {n : ℕ} {v : FK.boxVerts 3 n}
    {zero_noneA two_noneA two_endpointA two_originA two_ghostA
      two_ghost_endpointA two_ghost_originA : ℝ}
    {zero_noneB two_noneB two_endpointB two_originB two_ghostB
      two_ghost_endpointB two_ghost_originB : ℝ}
    {fourA fourB : Bool → Bool → Bool → ℕ → ℝ}
    (hzeroNone : zero_noneA ≤ zero_noneB)
    (htwoNone : two_noneA ≤ two_noneB)
    (htwoEndpoint : two_endpointA ≤ two_endpointB)
    (htwoOrigin : two_originA ≤ two_originB)
    (htwoGhost : two_ghostA ≤ two_ghostB)
    (htwoGhostEndpoint : two_ghost_endpointA ≤ two_ghost_endpointB)
    (htwoGhostOrigin : two_ghost_originA ≤ two_ghost_originB)
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          fourA hasGhost hasOrigin hasEndpoint k ≤
            fourB hasGhost hasOrigin hasEndpoint k) :
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_noneA two_noneA two_endpointA two_originA two_ghostA
        two_ghost_endpointA two_ghost_originA fourA ≤
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_noneB two_noneB two_endpointB two_originB two_ghostB
        two_ghost_endpointB two_ghost_originB fourB := by
  let ShA :=
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zero_noneA two_noneA two_endpointA two_originA two_ghostA
      two_ghost_endpointA two_ghost_originA fourA
  let ShB :=
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zero_noneB two_noneB two_endpointB two_originB two_ghostB
      two_ghost_endpointB two_ghost_originB fourB
  have hfield :
      SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
        ShA.toBudget15 ShB.toBudget15 := by
    simpa [ShA, ShB] using
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_toBudget15_fieldwiseLe
        (v := v) hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
        htwoGhostEndpoint htwoGhostOrigin hfour
  have htotal :
      ShA.toBudget15.total ≤ ShB.toBudget15.total :=
    SourceClassEndpointMembershipLiveBudget15.total_le_of_fieldwiseLe hfield
  simpa [
    ShA,
    ShB,
    SourceClassEndpointMembershipResidualShellShare15.toBudget15_total,
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare_total_eq_expandedOfFourShareTotal] using
    htotal

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_lt_of_fourShare_le
    {n : ℕ} {v : FK.boxVerts 3 n}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin bound : ℝ}
    {fourA fourB : Bool → Bool → Bool → ℕ → ℝ}
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          fourA hasGhost hasOrigin hasEndpoint k ≤
            fourB hasGhost hasOrigin hasEndpoint k)
    (hstrict :
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
          v zero_none two_none two_endpoint two_origin two_ghost
          two_ghost_endpoint two_ghost_origin fourB < bound) :
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin fourA < bound :=
  lt_of_le_of_lt
    (SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_mono
      (v := v) (zero_noneA := zero_none) (zero_noneB := zero_none)
      (two_noneA := two_none) (two_noneB := two_none)
      (two_endpointA := two_endpoint) (two_endpointB := two_endpoint)
      (two_originA := two_origin) (two_originB := two_origin)
      (two_ghostA := two_ghost) (two_ghostB := two_ghost)
      (two_ghost_endpointA := two_ghost_endpoint)
      (two_ghost_endpointB := two_ghost_endpoint)
      (two_ghost_originA := two_ghost_origin)
      (two_ghost_originB := two_ghost_origin)
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl hfour)
    hstrict

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg_of_residualEnvelopeClassifiedCardFourMajorant
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {residualEnvelope :
      Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → ℝ}
    (hzeroNone : 0 ≤ zero_none)
    (htwoNone : 0 ≤ two_none)
    (htwoEndpoint : 0 ≤ two_endpoint)
    (htwoOrigin : 0 ≤ two_origin)
    (htwoGhost : 0 ≤ two_ghost)
    (htwoGhostEndpoint : 0 ≤ two_ghost_endpoint)
    (htwoGhostOrigin : 0 ≤ two_ghost_origin)
    (henv :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          ∀ R,
            R ∈
                finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                  v k →
              0 ≤ residualEnvelope hasGhost hasOrigin hasEndpoint R) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin
        (SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
          v Ω residualEnvelope) := by
  exact
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg
      (v := v)
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin
      (fun hasGhost hasOrigin hasEndpoint k hk =>
        SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant_nonneg
          (v := v) (Ω := Ω) (residualEnvelope := residualEnvelope)
          (hasGhost := hasGhost) (hasOrigin := hasOrigin)
          (hasEndpoint := hasEndpoint) (k := k)
          (henv hasGhost hasOrigin hasEndpoint k hk))

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg_of_pointwiseClassifiedFourMajorant
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {pointMajorant :
      ∀ (_ : Bool) (_ : Bool) (_ : Bool)
        (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    (hzeroNone : 0 ≤ zero_none)
    (htwoNone : 0 ≤ two_none)
    (htwoEndpoint : 0 ≤ two_endpoint)
    (htwoOrigin : 0 ≤ two_origin)
    (htwoGhost : 0 ≤ two_ghost)
    (htwoGhostEndpoint : 0 ≤ two_ghost_endpoint)
    (htwoGhostOrigin : 0 ≤ two_ghost_origin)
    (hpoint :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          ∀ R,
            R ∈
                finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                  v k →
              ∀ E,
                E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ω hasGhost hasOrigin hasEndpoint R →
                  0 ≤ pointMajorant hasGhost hasOrigin hasEndpoint R E) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin
        (SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
          v Ω pointMajorant) := by
  exact
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg
      (v := v)
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin
      (fun hasGhost hasOrigin hasEndpoint k hk =>
        SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant_nonneg
          (v := v) (Ω := Ω) (pointMajorant := pointMajorant)
          (hasGhost := hasGhost) (hasOrigin := hasOrigin)
          (hasEndpoint := hasEndpoint) (k := k)
          (hpoint hasGhost hasOrigin hasEndpoint k hk))

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg_of_residualEnvelopeClassifiedCardFourMajorant_summandBounds
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {residualEnvelope :
      Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → ℝ}
    (hzeroNone : 0 ≤ zero_none)
    (htwoNone : 0 ≤ two_none)
    (htwoEndpoint : 0 ≤ two_endpoint)
    (htwoOrigin : 0 ≤ two_origin)
    (htwoGhost : 0 ≤ two_ghost)
    (htwoGhostEndpoint : 0 ≤ two_ghost_endpoint)
    (htwoGhostOrigin : 0 ≤ two_ghost_origin)
    (henv :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          ∀ R,
            R ∈
                finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                  v k →
              ∀ E,
                E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ω hasGhost hasOrigin hasEndpoint R →
                  finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E ≤
                    residualEnvelope hasGhost hasOrigin hasEndpoint R) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin
        (SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
          v Ω residualEnvelope) := by
  exact
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg
      (v := v)
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin
      (fun hasGhost hasOrigin hasEndpoint k hk =>
        SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant_nonneg_of_summandBounds
          (β := β) (H := H) hβ hH (v := v) (Ω := Ω)
          (residualEnvelope := residualEnvelope)
          (hasGhost := hasGhost) (hasOrigin := hasOrigin)
          (hasEndpoint := hasEndpoint) (k := k)
          (henv hasGhost hasOrigin hasEndpoint k hk))

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg_of_pointwiseClassifiedFourMajorant_summandBounds
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {pointMajorant :
      ∀ (_ : Bool) (_ : Bool) (_ : Bool)
        (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    (hzeroNone : 0 ≤ zero_none)
    (htwoNone : 0 ≤ two_none)
    (htwoEndpoint : 0 ≤ two_endpoint)
    (htwoOrigin : 0 ≤ two_origin)
    (htwoGhost : 0 ≤ two_ghost)
    (htwoGhostEndpoint : 0 ≤ two_ghost_endpoint)
    (htwoGhostOrigin : 0 ≤ two_ghost_origin)
    (hpoint :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          ∀ R,
            R ∈
                finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                  v k →
              ∀ E,
                E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ω hasGhost hasOrigin hasEndpoint R →
                  finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E ≤
                    pointMajorant hasGhost hasOrigin hasEndpoint R E) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin
        (SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
          v Ω pointMajorant) := by
  exact
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg
      (v := v)
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin
      (fun hasGhost hasOrigin hasEndpoint k hk =>
        SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant_nonneg_of_summandBounds
          (β := β) (H := H) hβ hH (v := v) (Ω := Ω)
          (pointMajorant := pointMajorant)
          (hasGhost := hasGhost) (hasOrigin := hasOrigin)
          (hasEndpoint := hasEndpoint) (k := k)
          (hpoint hasGhost hasOrigin hasEndpoint k hk))

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_mono_residualEnvelopeClassifiedCardFourMajorant
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {zero_noneA two_noneA two_endpointA two_originA two_ghostA
      two_ghost_endpointA two_ghost_originA : ℝ}
    {zero_noneB two_noneB two_endpointB two_originB two_ghostB
      two_ghost_endpointB two_ghost_originB : ℝ}
    {residualEnvelopeA residualEnvelopeB :
      Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → ℝ}
    (hzeroNone : zero_noneA ≤ zero_noneB)
    (htwoNone : two_noneA ≤ two_noneB)
    (htwoEndpoint : two_endpointA ≤ two_endpointB)
    (htwoOrigin : two_originA ≤ two_originB)
    (htwoGhost : two_ghostA ≤ two_ghostB)
    (htwoGhostEndpoint : two_ghost_endpointA ≤ two_ghost_endpointB)
    (htwoGhostOrigin : two_ghost_originA ≤ two_ghost_originB)
    (henv :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          ∀ R,
            R ∈
                finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                  v k →
              residualEnvelopeA hasGhost hasOrigin hasEndpoint R ≤
                residualEnvelopeB hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_noneA two_noneA two_endpointA two_originA two_ghostA
        two_ghost_endpointA two_ghost_originA
        (SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
          v Ω residualEnvelopeA) ≤
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_noneB two_noneB two_endpointB two_originB two_ghostB
        two_ghost_endpointB two_ghost_originB
        (SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
          v Ω residualEnvelopeB) := by
  exact
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_mono
      (v := v)
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin
      (fun hasGhost hasOrigin hasEndpoint k hk =>
        SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant_mono
          (v := v) (Ω := Ω)
          (residualEnvelopeA := residualEnvelopeA)
          (residualEnvelopeB := residualEnvelopeB)
          (hasGhost := hasGhost) (hasOrigin := hasOrigin)
          (hasEndpoint := hasEndpoint) (k := k)
          (henv hasGhost hasOrigin hasEndpoint k hk))

set_option linter.style.longLine false in


theorem
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_mono_pointwiseClassifiedFourMajorant
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {zero_noneA two_noneA two_endpointA two_originA two_ghostA
      two_ghost_endpointA two_ghost_originA : ℝ}
    {zero_noneB two_noneB two_endpointB two_originB two_ghostB
      two_ghost_endpointB two_ghost_originB : ℝ}
    {pointMajorantA pointMajorantB :
      ∀ (_ : Bool) (_ : Bool) (_ : Bool)
        (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    (hzeroNone : zero_noneA ≤ zero_noneB)
    (htwoNone : two_noneA ≤ two_noneB)
    (htwoEndpoint : two_endpointA ≤ two_endpointB)
    (htwoOrigin : two_originA ≤ two_originB)
    (htwoGhost : two_ghostA ≤ two_ghostB)
    (htwoGhostEndpoint : two_ghost_endpointA ≤ two_ghost_endpointB)
    (htwoGhostOrigin : two_ghost_originA ≤ two_ghost_originB)
    (hpoint :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          ∀ R,
            R ∈
                finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                  v k →
              ∀ E,
                E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ω hasGhost hasOrigin hasEndpoint R →
                  pointMajorantA hasGhost hasOrigin hasEndpoint R E ≤
                    pointMajorantB hasGhost hasOrigin hasEndpoint R E) :
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_noneA two_noneA two_endpointA two_originA two_ghostA
        two_ghost_endpointA two_ghost_originA
        (SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
          v Ω pointMajorantA) ≤
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_noneB two_noneB two_endpointB two_originB two_ghostB
        two_ghost_endpointB two_ghost_originB
        (SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
          v Ω pointMajorantB) := by
  exact
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_mono
      (v := v)
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin
      (fun hasGhost hasOrigin hasEndpoint k hk =>
        SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant_mono
          (v := v) (Ω := Ω)
          (pointMajorantA := pointMajorantA)
          (pointMajorantB := pointMajorantB)
          (hasGhost := hasGhost) (hasOrigin := hasOrigin)
          (hasEndpoint := hasEndpoint) (k := k)
          (hpoint hasGhost hasOrigin hasEndpoint k hk))

set_option linter.style.longLine false in

theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R} :
    (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell
      v β H Ω ι label).Nonneg := by
  classical
  have hB :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
      hβ hH n Ω v
  rcases hB with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, _hfourNoneBudget,
      _hfourEndpointBudget, _hfourOriginBudget, _hfourOriginEndpointBudget,
      _hfourGhostBudget, _hfourGhostEndpointBudget,
      _hfourGhostOriginBudget, _hfourGhostOriginEndpointBudget⟩
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _hk
    dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)))
  · intro k _hk
    dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)))
  · intro k _hk
    dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)))
  · intro k _hk
    dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)))
  · intro k _hk
    dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)))
  · intro k _hk
    dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)))
  · intro k _hk
    dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)))
  · intro k _hk
    dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare]
    exact Finset.sum_nonneg (fun R _hR =>
      Finset.sum_nonneg (fun i _hi =>
        Finset.sum_nonneg (fun E _hE =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)))

set_option linter.style.longLine false in

theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R} :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
        v β H Ω ι label := by
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell
      v β H Ω ι label
  have hshell : shellShare.Nonneg := by
    simpa [shellShare] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_nonneg
        (v := v) (β := β) (H := H) (Ω := Ω)
        (ι := ι) (label := label) hβ hH
  have htotal : 0 ≤ shellShare.total :=
    SourceClassEndpointMembershipLiveBudget15.total_nonneg
      (SourceClassEndpointMembershipResidualShellShare15.toBudget15_nonneg
        hshell)
  simpa [shellShare,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_total]
    using htotal

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {share : ℕ → ℝ}
    (h :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint →
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k ≤ share k * D) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint ≤
      (∑ k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint,
        share k) * D := by
  classical
  calc
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint
        =
          ∑ k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint,
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
              β H n Ω v hasGhost hasOrigin hasEndpoint k := by
          simp [
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum]
    _ ≤
          ∑ k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint,
            share k * D := by
          exact Finset.sum_le_sum (fun k hk => h k hk)
    _ =
        (∑ k ∈
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
            v hasGhost hasOrigin hasEndpoint,
          share k) * D := by
      exact
        (Finset.sum_mul
          (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
            v hasGhost hasOrigin hasEndpoint) share D).symm

end Exact3D
end StatMech
