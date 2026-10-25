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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part60
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.rawFieldwiseLe_of_labelFreeRawFieldwiseLe
    {β H : ℝ} {n : ℕ}
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
          ι hasGhost hasOrigin hasEndpoint R}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (h :
      Sh.LabelFreeRawFieldwiseLe β H Ω) :
    Sh.RawFieldwiseLe β H Ω ι label := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourNone k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourEndpoint k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourOrigin k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourOriginEndpoint k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourGhost k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourGhostEndpoint k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourGhostOrigin k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourGhostOriginEndpoint k hk

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFieldwiseLe_of_rawFieldwiseLe
    {β H : ℝ} {n : ℕ}
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
          ι hasGhost hasOrigin hasEndpoint R}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (h :
      Sh.RawFieldwiseLe β H Ω ι label) :
    Sh.LabelFreeRawFieldwiseLe β H Ω := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourNone k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourEndpoint k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourOrigin k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourOriginEndpoint k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourGhost k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourGhostEndpoint k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourGhostOrigin k hk
  · intro k hk
    simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
      using hfourGhostOriginEndpoint k hk

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.rawFieldwiseLe_iff_labelFreeRawFieldwiseLe
    {β H : ℝ} {n : ℕ}
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
          ι hasGhost hasOrigin hasEndpoint R}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v} :
    Sh.RawFieldwiseLe β H Ω ι label ↔
      Sh.LabelFreeRawFieldwiseLe β H Ω := by
  constructor
  · exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFieldwiseLe_of_rawFieldwiseLe
  · exact
      SourceClassEndpointMembershipResidualShellShare15.rawFieldwiseLe_of_labelFreeRawFieldwiseLe

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.rawFieldwiseLe_of_fields
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {fourMajorant : Bool → Bool → Bool → ℕ → ℝ}
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
          ι hasGhost hasOrigin hasEndpoint R}
    (hzeroNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).zero_none ≤ zero_none)
    (htwoNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_none ≤ two_none)
    (htwoEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_endpoint ≤ two_endpoint)
    (htwoOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_origin ≤ two_origin)
    (htwoGhost :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost ≤ two_ghost)
    (htwoGhostEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_endpoint ≤ two_ghost_endpoint)
    (htwoGhostOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_origin ≤ two_ghost_origin)
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
            v β H Ω ι label hasGhost hasOrigin hasEndpoint k ≤
            fourMajorant hasGhost hasOrigin hasEndpoint k) :
    (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin fourMajorant).RawFieldwiseLe
        β H Ω ι label := by
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


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFieldwiseLe_of_fields
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {fourMajorant : Bool → Bool → Bool → ℕ → ℝ}
    (hzeroNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).zero_none ≤ zero_none)
    (htwoNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_none ≤ two_none)
    (htwoEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_endpoint ≤ two_endpoint)
    (htwoOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_origin ≤ two_origin)
    (htwoGhost :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost ≤ two_ghost)
    (htwoGhostEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_endpoint ≤ two_ghost_endpoint)
    (htwoGhostOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_origin ≤ two_ghost_origin)
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
            v β H Ω hasGhost hasOrigin hasEndpoint k ≤
            fourMajorant hasGhost hasOrigin hasEndpoint k) :
    (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin fourMajorant).LabelFreeRawFieldwiseLe
        β H Ω := by
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


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFieldwiseLe_of_IccExactCardImageSourceClassSum_bounds_of_boundary
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {fourMajorant : Bool → Bool → Bool → ℕ → ℝ}
    (hzeroNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).zero_none ≤ zero_none)
    (htwoNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_none ≤ two_none)
    (htwoEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_endpoint ≤ two_endpoint)
    (htwoOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_origin ≤ two_origin)
    (htwoGhost :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost ≤ two_ghost)
    (htwoGhostEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_endpoint ≤ two_ghost_endpoint)
    (htwoGhostOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_origin ≤ two_ghost_origin)
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            Finset.Icc
              (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                hasGhost hasOrigin hasEndpoint)
              ((2 * n + 1) ^ 3 - 2) →
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v hasGhost hasOrigin hasEndpoint k ≤
            fourMajorant hasGhost hasOrigin hasEndpoint k) :
    (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin fourMajorant).LabelFreeRawFieldwiseLe
        β H Ω := by
  exact
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFieldwiseLe_of_fields
      (v := v) (β := β) (H := H) (Ω := Ω)
      (zero_none := zero_none) (two_none := two_none)
      (two_endpoint := two_endpoint) (two_origin := two_origin)
      (two_ghost := two_ghost)
      (two_ghost_endpoint := two_ghost_endpoint)
      (two_ghost_origin := two_ghost_origin)
      (fourMajorant := fourMajorant)
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin
      (fun hasGhost hasOrigin hasEndpoint k hk => by
        have hkIcc :
            k ∈
              Finset.Icc
                (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                  hasGhost hasOrigin hasEndpoint)
                ((2 * n + 1) ^ 3 - 2) := by
          simpa [
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
              hv hasGhost hasOrigin hasEndpoint] using hk
        rw [
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_markedResidualExactCardImageSourceClassSum
            β H n Ω v hasGhost hasOrigin hasEndpoint k]
        exact hfour hasGhost hasOrigin hasEndpoint k hkIcc)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_rawFieldwiseLe
    {β H : ℝ} {n : ℕ}
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
        v β H Ω ι label).RawFieldwiseLe β H Ω ι label := by
  refine
    ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell_labelFreeRawFieldwiseLe
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n} :
    (SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell
        v β H Ω).LabelFreeRawFieldwiseLe β H Ω := by
  refine
    ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_fieldwiseLe_toBudget15_of_rawFieldwiseLe
    {β H : ℝ} {n : ℕ}
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
          ι hasGhost hasOrigin hasEndpoint R}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (h :
      Sh.RawFieldwiseLe β H Ω ι label) :
    SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
      (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
        v β H Ω ι label)
      Sh.toBudget15 := by
  classical
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      hzeroNone
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoNone
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoEndpoint
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoOrigin
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhost
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhostEndpoint
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhostOrigin
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourNone
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourEndpoint
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourOrigin
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourOriginEndpoint
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourGhost
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourGhostEndpoint
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourGhostOrigin
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourGhostOriginEndpoint

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15_fieldwiseLe_toBudget15_of_labelFreeRawFieldwiseLe
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (h :
      Sh.LabelFreeRawFieldwiseLe β H Ω) :
    SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
      (SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
        v β H Ω)
      Sh.toBudget15 := by
  classical
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      hzeroNone
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoNone
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoEndpoint
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoOrigin
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhost
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhostEndpoint
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15] using
      htwoGhostOrigin
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourNone
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourEndpoint
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourOrigin
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourOriginEndpoint
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourGhost
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourGhostEndpoint
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourGhostOrigin
  · dsimp [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
    exact Finset.sum_le_sum hfourGhostOriginEndpoint

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRows_total_mul_eq_rawTotal
    {β H D : ℝ} (hDne : D ≠ 0) {n : ℕ}
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
        v β H D Ω ι label).total * D =
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
        v β H Ω ι label := by
  unfold SourceClassEndpointMembershipResidualShellShare15.total
  unfold SourceClassEndpointMembershipResidualShellShare15.toBudget15
  unfold SourceClassEndpointMembershipLiveBudget15.total
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRows
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
  simp_rw [← Finset.sum_div]
  field_simp [hDne]

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.toBudget15_total
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v) :
    Sh.toBudget15.total = Sh.total := rfl

end Exact3D
end StatMech
