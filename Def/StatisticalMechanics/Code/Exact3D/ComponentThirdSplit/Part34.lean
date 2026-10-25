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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part31
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let sourceClassSupport :=
              finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
                n Ωnz v
            let denom :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            ∃ B : SourceClassEndpointMembershipLiveBudget15,
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.zero false false false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.zero_none ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.two false false false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.two_none ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.two false false true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.two_endpoint ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.two false true false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.two_origin ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.two true false false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.two_ghost ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.two true false true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.two_ghost_endpoint ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.two true true false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.two_ghost_origin ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus false false false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.four_none ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus false false true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.four_endpoint ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus false true false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.four_origin ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus false true true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.four_origin_endpoint ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus true false false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.four_ghost ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus true false true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.four_ghost_endpoint ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus true true false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.four_ghost_origin ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus true true true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                B.four_ghost_origin_endpoint ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  B.total ≤
                denom

end Exact3D
end StatMech
