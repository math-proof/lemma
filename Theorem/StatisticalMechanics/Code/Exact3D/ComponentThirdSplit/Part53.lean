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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part55
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_eq_labelFreeRawBudget15
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
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
        v β H Ω ι label =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
        v β H Ω := by
  simp [
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_eq_residualThresholdShellBudget15_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
        v β H Ω ι label =
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v := by
  classical
  simp [
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
    finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
      β H n Ω v hv label false false false,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
      β H n Ω v hv label false false true,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
      β H n Ω v hv label false true false,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
      β H n Ω v hv label false true true,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
      β H n Ω v hv label true false false,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
      β H n Ω v hv label true false true,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
      β H n Ω v hv label true true false,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
      β H n Ω v hv label true true true]

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_fieldwiseLe_residualThresholdShellBudget15_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
      (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
        v β H Ω ι label)
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v) := by
  classical
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
  · simp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
  · simp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
  · simp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
  · simp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
  · simp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
  · simp [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
      (le_of_eq
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
          β H n Ω v hv label false false false))
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
      (le_of_eq
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
          β H n Ω v hv label false false true))
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
      (le_of_eq
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
          β H n Ω v hv label false true false))
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
      (le_of_eq
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
          β H n Ω v hv label false true true))
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
      (le_of_eq
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
          β H n Ω v hv label true false false))
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
      (le_of_eq
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
          β H n Ω v hv label true false true))
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
      (le_of_eq
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
          β H n Ω v hv label true true false))
  · simpa [
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
      (le_of_eq
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
          β H n Ω v hv label true true true))

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.residualThresholdShellBudget15_fieldwiseLe_normalizedRowsRawBudget15_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v)
      (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
        v β H Ω ι label) := by
  rw [
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_eq_residualThresholdShellBudget15_of_boundary
      β H n Ω v hv label]
  exact
    ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
      le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
      le_rfl⟩

end Exact3D
end StatMech
