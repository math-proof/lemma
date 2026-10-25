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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part71
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCapPoint_mem
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCapPoint
        β H n Ω v hv ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v := by
  exact
    (Classical.choose_spec
      (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCapPoint_exists
        β H n Ω v hv)).1

end Exact3D
end StatMech
