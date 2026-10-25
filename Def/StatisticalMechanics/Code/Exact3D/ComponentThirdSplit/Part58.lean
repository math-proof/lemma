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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part55
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
    {n : ℕ} (v : FK.boxVerts 3 n)
    (zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ)
    (fourShare : Bool → Bool → Bool → ℕ → ℝ) : ℝ :=
  zero_none +
    two_none +
    two_endpoint +
    two_origin +
    two_ghost +
    two_ghost_endpoint +
    two_ghost_origin +
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false,
      fourShare false false false k) +
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true,
      fourShare false false true k) +
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false,
      fourShare false true false k) +
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true,
      fourShare false true true k) +
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false,
      fourShare true false false k) +
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true,
      fourShare true false true k) +
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false,
      fourShare true true false k) +
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true,
      fourShare true true true k)

end Exact3D
end StatMech
