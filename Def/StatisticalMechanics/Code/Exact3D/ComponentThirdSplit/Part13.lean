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
import Instance.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def finiteBoundaryGhostSourceClassEndpointMembershipLabel
    (cardCase : SourceClassCardinalityCase)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    SourceClassEndpointMembershipCase where
  cardCase := cardCase
  hasGhost := hasGhost
  hasOrigin := hasOrigin
  hasEndpoint := hasEndpoint

end Exact3D
end StatMech
