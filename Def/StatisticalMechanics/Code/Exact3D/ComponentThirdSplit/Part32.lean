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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part29
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipLiveBudget15.FieldwiseLeMul
    (B share : SourceClassEndpointMembershipLiveBudget15) (D : ℝ) : Prop :=
  B.zero_none ≤ share.zero_none * D ∧
    B.two_none ≤ share.two_none * D ∧
    B.two_endpoint ≤ share.two_endpoint * D ∧
    B.two_origin ≤ share.two_origin * D ∧
    B.two_ghost ≤ share.two_ghost * D ∧
    B.two_ghost_endpoint ≤ share.two_ghost_endpoint * D ∧
    B.two_ghost_origin ≤ share.two_ghost_origin * D ∧
    B.four_none ≤ share.four_none * D ∧
    B.four_endpoint ≤ share.four_endpoint * D ∧
    B.four_origin ≤ share.four_origin * D ∧
    B.four_origin_endpoint ≤ share.four_origin_endpoint * D ∧
    B.four_ghost ≤ share.four_ghost * D ∧
    B.four_ghost_endpoint ≤ share.four_ghost_endpoint * D ∧
    B.four_ghost_origin ≤ share.four_ghost_origin * D ∧
    B.four_ghost_origin_endpoint ≤ share.four_ghost_origin_endpoint * D

end Exact3D
end StatMech
