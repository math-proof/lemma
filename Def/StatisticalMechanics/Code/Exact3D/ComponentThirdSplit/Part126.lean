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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part119
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExplicitMajorantWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ fourMajorant : Bool → Bool → Bool → ℕ → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
                      v β H Ωnz hasGhost hasOrigin hasEndpoint k ≤
                      fourMajorant hasGhost hasOrigin hasEndpoint k) ∧
                (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                  v zero_none two_none two_endpoint two_origin two_ghost
                  two_ghost_endpoint two_ghost_origin fourMajorant).total ≤
                  slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExpandedMajorantWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ fourMajorant : Bool → Bool → Bool → ℕ → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
                      v β H Ωnz hasGhost hasOrigin hasEndpoint k ≤
                      fourMajorant hasGhost hasOrigin hasEndpoint k) ∧
                SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
                  v zero_none two_none two_endpoint two_origin two_ghost
                  two_ghost_endpoint two_ghost_origin fourMajorant ≤
                  slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ fourMajorant : Bool → Bool → Bool → ℕ → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      Finset.Icc
                        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                          hasGhost hasOrigin hasEndpoint)
                        ((2 * n + 1) ^ 3 - 2) →
                    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                      β H n Ωnz v hasGhost hasOrigin hasEndpoint k ≤
                      fourMajorant hasGhost hasOrigin hasEndpoint k) ∧
                SourceClassEndpointMembershipResidualShellShare15.expandedIccOfFourShareTotal
                  n zero_none two_none two_endpoint two_origin two_ghost
                  two_ghost_endpoint two_ghost_origin fourMajorant ≤
                  slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ fourMajorant : Bool → Bool → Bool → ℕ → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ k, k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v false false false k ≤
                    fourMajorant false false false k) ∧
                (∀ k, k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v false false true k ≤
                    fourMajorant false false true k) ∧
                (∀ k, k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v false true false k ≤
                    fourMajorant false true false k) ∧
                (∀ k, k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v false true true k ≤
                    fourMajorant false true true k) ∧
                (∀ k, k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v true false false k ≤
                    fourMajorant true false false k) ∧
                (∀ k, k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v true false true k ≤
                    fourMajorant true false true k) ∧
                (∀ k, k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v true true false k ≤
                    fourMajorant true true false k) ∧
                (∀ k, k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v true true true k ≤
                    fourMajorant true true true k) ∧
                SourceClassEndpointMembershipResidualShellShare15.expandedIccOfFourShareTotal
                  n zero_none two_none two_endpoint two_origin two_ghost
                  two_ghost_endpoint two_ghost_origin fourMajorant ≤
                  slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalTotalWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal
              β H n Ωnz v ≤
              slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                β H n Ωnz v +
              finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution
                β H n Ωnz v ≤
              slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                β H n Ωnz v +
              (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
                  β H n Ωnz v +
                finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                  β H n Ωnz v) ≤
              slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                β H n Ωnz v +
              (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
                  β H n Ωnz v +
                finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                  β H n Ωnz v) ≤
              slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTailWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            ∃ singletonBudget : Option (FK.boxVerts 3 n) → ℝ,
              (∀ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v
                  (finiteBoundaryGhostSourceClassEndpointMarkedSources
                      v true true true ∪
                    ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
                  singletonBudget x) ∧
                finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                    β H n Ωnz v +
                  ((∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
                      singletonBudget x) +
                    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                      β H n Ωnz v) ≤
                  slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            ∃ singletonBudget : Option (FK.boxVerts 3 n) → ℝ,
              (∀ x ∈ liveOptions,
                finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                    β H n Ωnz v
                    (finiteBoundaryGhostSourceClassEndpointMarkedSources
                        v true true true ∪
                      ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
                  singletonBudget x) ∧
                finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                    β H n Ωnz v +
                  ((∑ x ∈ liveOptions, singletonBudget x) +
                    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                      β H n Ωnz v) ≤
                  slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            ∃ remainingBudget tailBudget : ℝ,
              ∃ singletonBudget : Option (FK.boxVerts 3 n) → ℝ,
                finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                    β H n Ωnz v ≤ remainingBudget ∧
                  finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                      β H n Ωnz v ≤ tailBudget ∧
                    (∀ x ∈ liveOptions,
                      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                          β H n Ωnz v
                          (finiteBoundaryGhostSourceClassEndpointMarkedSources
                              v true true true ∪
                            ({x} :
                              Finset (Option (FK.boxVerts 3 n)))) ≤
                        singletonBudget x) ∧
                      remainingBudget +
                          ((∑ x ∈ liveOptions, singletonBudget x) +
                            tailBudget) ≤
                        slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailWeightNonzeroPositiveSubcritical
    (budget : LiveSingletonOptionComponentBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                β H n Ωnz v ≤ budget.remainingBudget β H Ωnz v ∧
              finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                  β H n Ωnz v ≤ budget.tailBudget β H Ωnz v ∧
                (∀ x ∈ liveOptions,
                  finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                      β H n Ωnz v
                      (finiteBoundaryGhostSourceClassEndpointMarkedSources
                          v true true true ∪
                        ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
                    budget.singletonBudget β H Ωnz v x) ∧
                  budget.remainingBudget β H Ωnz v +
                      ((∑ x ∈ liveOptions,
                          budget.singletonBudget β H Ωnz v x) +
                        budget.tailBudget β H Ωnz v) ≤
                    slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentWeightNonzeroPositiveSubcritical
    (budget : LiveSingletonOptionComponentBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            budget.remainingBudget β H Ωnz v +
                ((∑ x ∈ liveOptions,
                    budget.singletonBudget β H Ωnz v x) +
                  budget.tailBudget β H Ωnz v) ≤
              slack

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
    (schedule : LiveSingletonOptionShareSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            schedule.remainingShare β H Ωnz v * R +
                ((∑ x ∈ liveOptions,
                    schedule.singletonShare β H Ωnz v x * R) +
                  schedule.tailShare β H Ωnz v * R) ≤
              slack

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                β H n Ωnz v +
                ((∑ x ∈ liveOptions,
                    ∑ E ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                        v Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n))),
                      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                        β H E) +
                  finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                    β H n Ωnz v) ≤
              slack

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let slack :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                  β H n Ωnz v -
                finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                  β H n Ωnz v
            R ≤ slack

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let profile :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                β H n Ωnz v
            let active :=
              finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                β H n Ωnz v
            D + active ≤ paid + profile

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let profile :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                β H n Ωnz v
            let active :=
              finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
                β H n Ωnz v
            R + active ≤ profile

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let profile :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                β H n Ωnz v
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            R +
                (∑ d ∈ I.image,
                  (((I.fiber d).card : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)) ≤
              profile

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            R +
                (∑ d ∈ I.image,
                  ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))) ≤
              (I.image.card : ℝ) *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            R +
                ((∑ d ∈ I.image,
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)) +
                  (∑ d ∈ I.image,
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)) ≤
              (I.image.card : ℝ) *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            R ≤
              (∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))) +
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v -
                  (∑ d ∈ I.image,
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            ∃ mainShare : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ,
              ∃ emptyShare : ℝ,
                (∀ d, d ∈ I.image → 0 ≤ mainShare d) ∧
                0 ≤ emptyShare ∧
                R ≤ (∑ d ∈ I.image, mainShare d) + emptyShare ∧
                (∀ d, d ∈ I.image → mainShare d ≤ mainGap d) ∧
                emptyShare ≤ emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainGapSum :=
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            ∃ mainMass emptyMass : ℝ,
              0 ≤ mainMass ∧
                0 ≤ emptyMass ∧
                R ≤ mainMass + emptyMass ∧
                mainMass ≤ mainGapSum ∧
                emptyMass ≤ emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderNonpositiveWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            D - paid ≤ 0

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainGapSumWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            R ≤
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedEmptyGapWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            R ≤
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)


end Exact3D
end StatMech
