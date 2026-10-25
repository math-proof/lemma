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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part52
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_markedResidualExactCardImageSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k := by
  classical
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_unmarkedResidualExactCardSet_sum]
  unfold SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
  apply Finset.sum_congr rfl
  intro R _hR
  exact
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
      β H n Ω v hasGhost hasOrigin hasEndpoint R).symm

set_option linter.style.longLine false in

theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_zero_of_boundary_of_threshold_add_k_odd
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hodd :
      Odd
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint +
          k)) :
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k =
      0 := by
  rw [
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_markedResidualExactCardImageSourceClassSum]
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_zero_of_boundary_of_threshold_add_k_odd
      β H n Ω hv hasGhost hasOrigin hasEndpoint hodd

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k) =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint := by
  classical
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
  apply Finset.sum_congr rfl
  intro k _hk
  exact
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_markedResidualExactCardImageSourceClassSum
      β H n Ω v hasGhost hasOrigin hasEndpoint k

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_shellSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k) =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
  calc
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k)
        =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint := by
        exact
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum
            β H n Ω v hasGhost hasOrigin hasEndpoint
    _ =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
        exact
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
            β H n Ω hv hasGhost hasOrigin hasEndpoint

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_labelFreeRawFourShare_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
          v β H Ω hasGhost hasOrigin hasEndpoint k := by
  calc
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S)
        =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
        exact
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
            β H n Ω hv hasGhost hasOrigin hasEndpoint
    _ =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
          v β H Ω hasGhost hasOrigin hasEndpoint k := by
        symm
        apply Finset.sum_congr rfl
        intro k _hk
        exact
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_markedResidualExactCardImageSourceClassSum
            β H n Ω v hasGhost hasOrigin hasEndpoint k

end Exact3D
end StatMech
