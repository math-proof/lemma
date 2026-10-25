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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part57
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.RawFieldwiseLe
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v)
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
          ι hasGhost hasOrigin hasEndpoint R) : Prop :=
  (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).zero_none ≤ Sh.zero_none ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_none ≤ Sh.two_none ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_endpoint ≤ Sh.two_endpoint ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_origin ≤ Sh.two_origin ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost ≤ Sh.two_ghost ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_endpoint ≤ Sh.two_ghost_endpoint ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false →
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label false false false k ≤ Sh.four_none k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true →
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label false false true k ≤ Sh.four_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false →
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label false true false k ≤ Sh.four_origin k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true →
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label false true true k ≤ Sh.four_origin_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false →
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label true false false k ≤ Sh.four_ghost k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true →
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label true false true k ≤ Sh.four_ghost_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false →
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label true true false k ≤ Sh.four_ghost_origin k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true →
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label true true true k ≤
          Sh.four_ghost_origin_endpoint k)

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.LabelFreeRawFieldwiseLe
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Prop :=
  (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).zero_none ≤ Sh.zero_none ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_none ≤ Sh.two_none ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_endpoint ≤ Sh.two_endpoint ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_origin ≤ Sh.two_origin ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost ≤ Sh.two_ghost ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_endpoint ≤ Sh.two_ghost_endpoint ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false →
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω false false false k ≤ Sh.four_none k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true →
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω false false true k ≤ Sh.four_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false →
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω false true false k ≤ Sh.four_origin k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true →
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω false true true k ≤ Sh.four_origin_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false →
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true false false k ≤ Sh.four_ghost k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true →
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true false true k ≤ Sh.four_ghost_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false →
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true true false k ≤ Sh.four_ghost_origin k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true →
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true true true k ≤
          Sh.four_ghost_origin_endpoint k)

end Exact3D
end StatMech
