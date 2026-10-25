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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part32
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem SourceClassEndpointMembershipLiveBudget15.total_le_mul_of_fieldwiseLeMul
    {B share : SourceClassEndpointMembershipLiveBudget15} {D : ℝ}
    (h :
      SourceClassEndpointMembershipLiveBudget15.FieldwiseLeMul
        B share D) :
    B.total ≤ share.total * D := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  calc
    B.total ≤
        share.zero_none * D +
          share.two_none * D +
          share.two_endpoint * D +
          share.two_origin * D +
          share.two_ghost * D +
          share.two_ghost_endpoint * D +
          share.two_ghost_origin * D +
          share.four_none * D +
          share.four_endpoint * D +
          share.four_origin * D +
          share.four_origin_endpoint * D +
          share.four_ghost * D +
          share.four_ghost_endpoint * D +
          share.four_ghost_origin * D +
          share.four_ghost_origin_endpoint * D := by
      simp [SourceClassEndpointMembershipLiveBudget15.total]
      linarith
    _ = share.total * D := by
      simp [SourceClassEndpointMembershipLiveBudget15.total]
      ring

end Exact3D
end StatMech
