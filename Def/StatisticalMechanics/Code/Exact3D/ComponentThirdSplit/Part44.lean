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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part41
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n)))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι)
    (labelShare : ι → ℝ) (D : ℝ) : Prop :=
  (∀ i, 0 ≤ labelShare i) ∧
    ∀ i,
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum
          v β H Ω hasGhost hasOrigin hasEndpoint R label i ≤
        labelShare i * D

end Exact3D
end StatMech
