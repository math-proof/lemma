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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part29
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipLiveBudget15.sum_liveCaseFinset_toBudget
    (B : SourceClassEndpointMembershipLiveBudget15) :
    (∑ c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
      B.toBudget c) = B.total := by
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel,
    SourceClassEndpointMembershipLiveBudget15.toBudget,
    SourceClassEndpointMembershipLiveBudget15.total]
  ring

end Exact3D
end StatMech
