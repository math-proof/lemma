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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part51
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell
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
    SourceClassEndpointMembershipResidualShellShare15 v where
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
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
      v β H Ω ι label false false false
  four_endpoint :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
      v β H Ω ι label false false true
  four_origin :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
      v β H Ω ι label false true false
  four_origin_endpoint :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
      v β H Ω ι label false true true
  four_ghost :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
      v β H Ω ι label true false false
  four_ghost_endpoint :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
      v β H Ω ι label true false true
  four_ghost_origin :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
      v β H Ω ι label true true false
  four_ghost_origin_endpoint :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
      v β H Ω ι label true true true

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    SourceClassEndpointMembershipResidualShellShare15 v where
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
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
      v β H Ω false false false
  four_endpoint :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
      v β H Ω false false true
  four_origin :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
      v β H Ω false true false
  four_origin_endpoint :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
      v β H Ω false true true
  four_ghost :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
      v β H Ω true false false
  four_ghost_endpoint :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
      v β H Ω true false true
  four_ghost_origin :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
      v β H Ω true true false
  four_ghost_origin_endpoint :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
      v β H Ω true true true

end Exact3D
end StatMech
