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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part59
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_eq_expandedIccOfFourShareTotal_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {fourShare : Bool → Bool → Bool → ℕ → ℝ} :
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
        v zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin fourShare =
      SourceClassEndpointMembershipResidualShellShare15.expandedIccOfFourShareTotal
        n zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin fourShare := by
  simp [
    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal,
    SourceClassEndpointMembershipResidualShellShare15.expandedIccOfFourShareTotal,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv false false false,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv false false true,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv false true false,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv false true true,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv true false false,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv true false true,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv true true false,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv true true true]

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_toBudget15
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
        v β H Ω ι label).toBudget15 =
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
        v β H Ω ι label := by
  rfl

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell_toBudget15
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n} :
    (SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell
        v β H Ω).toBudget15 =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
        v β H Ω := by
  rfl

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_total
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
        v β H Ω ι label).total =
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
        v β H Ω ι label := by
  simpa [
    SourceClassEndpointMembershipResidualShellShare15.total,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_toBudget15] using
    (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_total
      (v := v) (β := β) (H := H) (Ω := Ω)
      (ι := ι) (label := label))

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell_total
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n} :
    (SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell
        v β H Ω).total =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
        v β H Ω := by
  simpa [
    SourceClassEndpointMembershipResidualShellShare15.total,
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell_toBudget15] using
    (SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15_total
      (v := v) (β := β) (H := H) (Ω := Ω))

end Exact3D
end StatMech
