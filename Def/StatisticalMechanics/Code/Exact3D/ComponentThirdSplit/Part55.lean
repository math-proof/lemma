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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part52
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*)
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipLiveBudget15 where
  zero_none :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).zero_none
  two_none :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_none
  two_endpoint :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_endpoint
  two_origin :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_origin
  two_ghost :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost
  two_ghost_endpoint :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_endpoint
  two_ghost_origin :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_origin
  four_none :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label false false false k
  four_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label false false true k
  four_origin :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label false true false k
  four_origin_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label false true true k
  four_ghost :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label true false false k
  four_ghost_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label true false true k
  four_ghost_origin :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label true true false k
  four_ghost_origin_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label true true true k

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    SourceClassEndpointMembershipLiveBudget15 where
  zero_none :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).zero_none
  two_none :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_none
  two_endpoint :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_endpoint
  two_origin :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_origin
  two_ghost :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost
  two_ghost_endpoint :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_endpoint
  two_ghost_origin :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_origin
  four_none :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω false false false k
  four_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω false false true k
  four_origin :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω false true false k
  four_origin_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω false true true k
  four_ghost :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true false false k
  four_ghost_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true false true k
  four_ghost_origin :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true true false k
  four_ghost_origin_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true,
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true true true k

end Exact3D
end StatMech
