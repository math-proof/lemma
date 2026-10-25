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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part54
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.toBudget15
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v) :
    SourceClassEndpointMembershipLiveBudget15 where
  zero_none := Sh.zero_none
  two_none := Sh.two_none
  two_endpoint := Sh.two_endpoint
  two_origin := Sh.two_origin
  two_ghost := Sh.two_ghost
  two_ghost_endpoint := Sh.two_ghost_endpoint
  two_ghost_origin := Sh.two_ghost_origin
  four_none :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false,
      Sh.four_none k
  four_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true,
      Sh.four_endpoint k
  four_origin :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false,
      Sh.four_origin k
  four_origin_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true,
      Sh.four_origin_endpoint k
  four_ghost :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false,
      Sh.four_ghost k
  four_ghost_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true,
      Sh.four_ghost_endpoint k
  four_ghost_origin :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false,
      Sh.four_ghost_origin k
  four_ghost_origin_endpoint :=
    ∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true,
      Sh.four_ghost_origin_endpoint k

set_option linter.style.longLine false in

noncomputable def SourceClassEndpointMembershipResidualShellShare15.total
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v) : ℝ :=
  Sh.toBudget15.total

end Exact3D
end StatMech
