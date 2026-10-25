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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part112
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackAuxiliaryTwoSourceBudget15WeightNonzeroPositiveSubcritical :
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
            ∃ four_none four_endpoint four_origin four_origin_endpoint : ℝ,
            ∃ four_ghost four_ghost_endpoint four_ghost_origin : ℝ,
            ∃ four_ghost_origin_endpoint : ℝ,
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus false false false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                four_none ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus false false true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                four_endpoint ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus false true false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                four_origin ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus false true true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                four_origin_endpoint ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus true false false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                four_ghost ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus true false true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                four_ghost_endpoint ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus true true false),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                four_ghost_origin ∧
              (∑ S ∈ sourceClassSupport.filter
                  (fun S =>
                    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                      finiteBoundaryGhostSourceClassEndpointMembershipLabel
                        SourceClassCardinalityCase.fourPlus true true true),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                four_ghost_origin_endpoint ∧
              (finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15
                β H n Ωnz v
                four_none four_endpoint four_origin four_origin_endpoint
                four_ghost four_ghost_endpoint four_ghost_origin
                four_ghost_origin_endpoint).total ≤
                slack

end Exact3D
end StatMech
