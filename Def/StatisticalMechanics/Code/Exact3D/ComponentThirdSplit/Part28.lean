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
import Abbrev.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part2
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorptionPositiveSubcritical :
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
            ∃ coefficientBudget :
                Finset (Option (FK.boxVerts 3 n)) → ℝ,
              (∀ S, S ∈ sourceClassSupport →
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                    β H n Ωnz v S ≤
                  coefficientBudget S) ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  (∑ S ∈ sourceClassSupport, coefficientBudget S) ≤
                denom

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :
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
            0 < denom ∧
              ∃ coefficientBudget :
                  Finset (Option (FK.boxVerts 3 n)) → ℝ,
                (∀ S, S ∈ sourceClassSupport →
                  finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                      β H n Ωnz v S ≤
                    coefficientBudget S) ∧
                cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v +
                    (∑ S ∈ sourceClassSupport, coefficientBudget S) ≤
                  denom

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentShareAbsorptionPositiveSubcritical :
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
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
              ∃ coefficientShare :
                Finset (Option (FK.boxVerts 3 n)) → ℝ,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              (∀ S, S ∈ sourceClassSupport → 0 ≤ coefficientShare S) ∧
              oneShare + boundaryPairShare + emptyBoundaryShare +
                  (∑ S ∈ sourceClassSupport, coefficientShare S) ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * denom ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * denom ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * denom ∧
              ∀ S, S ∈ sourceClassSupport →
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                    β H n Ωnz v S ≤
                  coefficientShare S * denom

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorptionPositiveSubcritical :
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
            ∃ ghostBudget nonGhostBudget : ℝ,
              (∑ S ∈ sourceClassSupport.filter (fun S => none ∈ S),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                ghostBudget ∧
              (∑ S ∈ sourceClassSupport.filter (fun S => none ∉ S),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                nonGhostBudget ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  (ghostBudget + nonGhostBudget) ≤
                denom

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentShareAbsorptionPositiveSubcritical :
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
            ∃ oneShare boundaryPairShare emptyBoundaryShare ghostShare nonGhostShare : ℝ,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              0 ≤ ghostShare ∧
              0 ≤ nonGhostShare ∧
              oneShare + boundaryPairShare + emptyBoundaryShare +
                  (ghostShare + nonGhostShare) ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * denom ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * denom ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * denom ∧
              (∑ S ∈ sourceClassSupport.filter (fun S => none ∈ S),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                ghostShare * denom ∧
              (∑ S ∈ sourceClassSupport.filter (fun S => none ∉ S),
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v S) ≤
                nonGhostShare * denom

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportCardinalityComponentSumAbsorptionPositiveSubcritical :
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
            ∃ coefficientBudget : SourceClassCardinalityCase → ℝ,
              (∀ c,
                (∑ S ∈ sourceClassSupport.filter
                    (fun S => finiteBoundaryGhostSourceClassCardinalityCase S = c),
                  finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                    β H n Ωnz v S) ≤
                  coefficientBudget c) ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v +
                  (∑ c, coefficientBudget c) ≤
                denom

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorptionPositiveSubcritical :
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
            ∃ coefficientBudget : SourceClassEndpointMembershipCase → ℝ,
              (∀ c,
                (∑ S ∈ sourceClassSupport.filter
                    (fun S =>
                      finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
                  finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                    β H n Ωnz v S) ≤
                  coefficientBudget c) ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  (∑ c, coefficientBudget c) ≤
                denom

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical :
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
            ∃ coefficientBudget : SourceClassEndpointMembershipCase → ℝ,
              (∀ c,
                finiteBoundaryGhostSourceClassEndpointMembershipLiveCase c →
                  (∑ S ∈ sourceClassSupport.filter
                      (fun S =>
                        finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
                    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                      β H n Ωnz v S) ≤
                    coefficientBudget c) ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  (∑ c ∈
                    (Finset.univ : Finset SourceClassEndpointMembershipCase).filter
                      finiteBoundaryGhostSourceClassEndpointMembershipLiveCase,
                    coefficientBudget c) ≤
                denom

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical :
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
            ∃ coefficientBudget : SourceClassEndpointMembershipCase → ℝ,
              (∀ c,
                c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset →
                  (∑ S ∈ sourceClassSupport.filter
                      (fun S =>
                        finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
                    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                      β H n Ωnz v S) ≤
                    coefficientBudget c) ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  (∑ c ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
                    coefficientBudget c) ≤
                denom

end Exact3D
end StatMech
