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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part43
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ)
    (share D : ℝ) : Prop :=
  0 ≤ share ∧
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k ≤
      share * D

end Exact3D
end StatMech
