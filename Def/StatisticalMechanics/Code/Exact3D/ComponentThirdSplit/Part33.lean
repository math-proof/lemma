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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part30
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipLiveBudget15.normalized
    (B : SourceClassEndpointMembershipLiveBudget15) (D : ℝ) :
    SourceClassEndpointMembershipLiveBudget15 where
  zero_none := B.zero_none / D
  two_none := B.two_none / D
  two_endpoint := B.two_endpoint / D
  two_origin := B.two_origin / D
  two_ghost := B.two_ghost / D
  two_ghost_endpoint := B.two_ghost_endpoint / D
  two_ghost_origin := B.two_ghost_origin / D
  four_none := B.four_none / D
  four_endpoint := B.four_endpoint / D
  four_origin := B.four_origin / D
  four_origin_endpoint := B.four_origin_endpoint / D
  four_ghost := B.four_ghost / D
  four_ghost_endpoint := B.four_ghost_endpoint / D
  four_ghost_origin := B.four_ghost_origin / D
  four_ghost_origin_endpoint := B.four_ghost_origin_endpoint / D

end Exact3D
end StatMech
