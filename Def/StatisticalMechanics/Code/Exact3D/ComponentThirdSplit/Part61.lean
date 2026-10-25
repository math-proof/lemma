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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part58
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.Nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v) : Prop :=
  0 ≤ Sh.zero_none ∧
    0 ≤ Sh.two_none ∧
    0 ≤ Sh.two_endpoint ∧
    0 ≤ Sh.two_origin ∧
    0 ≤ Sh.two_ghost ∧
    0 ≤ Sh.two_ghost_endpoint ∧
    0 ≤ Sh.two_ghost_origin ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false → 0 ≤ Sh.four_none k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true → 0 ≤ Sh.four_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false → 0 ≤ Sh.four_origin k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true → 0 ≤ Sh.four_origin_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false → 0 ≤ Sh.four_ghost k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true → 0 ≤ Sh.four_ghost_endpoint k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false → 0 ≤ Sh.four_ghost_origin k) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true → 0 ≤ Sh.four_ghost_origin_endpoint k)

end Exact3D
end StatMech
