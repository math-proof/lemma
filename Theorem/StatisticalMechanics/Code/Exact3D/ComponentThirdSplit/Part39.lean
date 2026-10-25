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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part41
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet_mem_iff
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {R : Finset (Option (FK.boxVerts 3 n))} :
    R ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet
          v Ω hasGhost hasOrigin hasEndpoint k ↔
      R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k ∧
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).Nonempty := by
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet]

end Exact3D
end StatMech
