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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part32
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackExplicitLiveEndpointMembershipBudget15WeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let sourceClassSupport :=
              finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
                n Ωnz v
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            ∃ B : SourceClassEndpointMembershipLiveBudget15,
              (∀ c,
                c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset →
                  (∑ S ∈ sourceClassSupport.filter
                      (fun S =>
                        finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
                    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                      β H n Ωnz v S) ≤
                    B.toBudget c) ∧
              B.total ≤ slack

end Exact3D
end StatMech
