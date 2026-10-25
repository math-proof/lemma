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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part49
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.ofFourShare_fourShare
    {n : ℕ} {v : FK.boxVerts 3 n}
    {zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ}
    {fourShare : Bool → Bool → Bool → ℕ → ℝ}
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin fourShare).fourShare
        hasGhost hasOrigin hasEndpoint =
      fourShare hasGhost hasOrigin hasEndpoint := by
  cases hasGhost <;> cases hasOrigin <;> cases hasEndpoint <;> rfl

end Exact3D
end StatMech
