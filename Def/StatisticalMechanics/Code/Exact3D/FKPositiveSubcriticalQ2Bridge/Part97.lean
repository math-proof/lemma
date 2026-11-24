module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part94
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
            finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
              finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
            finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n
                (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) ≤
              finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          finiteBoundaryGhostBoundaryFiberDecomposedSourcePairBound β H n Ω ≤
            ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n =>
              FK.boxBoundary 3 n v),
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω ≤
            finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound
              β H n Ω ≤
            finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
              β H n Ω ≤
            finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
              β H n Ω ≤
            finiteCurrentBoundaryTwoPointSum β n *
              (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (∅ : Finset (Option (FK.boxVerts 3 n))) *
              Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (∅ : Finset (Option (FK.boxVerts 3 n))))


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∃ oneBudget boundaryPairBudget emptyBoundaryBudget : ℝ,
            finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent
                β H n Ω ≤ oneBudget ∧
            finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent
                β H n Ω ≤ boundaryPairBudget ∧
            finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent
                β H n Ω ≤ emptyBoundaryBudget ∧
            oneBudget + boundaryPairBudget + emptyBoundaryBudget ≤
              finiteCurrentBoundaryTwoPointSum β n *
                (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                  (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                  (∅ : Finset (Option (FK.boxVerts 3 n))) *
                Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                  (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                  (∅ : Finset (Option (FK.boxVerts 3 n))))


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
            0 ≤ oneShare ∧
            0 ≤ boundaryPairShare ∧
            0 ≤ emptyBoundaryShare ∧
            oneShare + boundaryPairShare + emptyBoundaryShare ≤ 1 ∧
            finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent
                β H n Ω ≤
              oneShare *
                finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator
                  β H n ∧
            finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent
                β H n Ω ≤
              boundaryPairShare *
                finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator
                  β H n ∧
            finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent
                β H n Ω ≤
              emptyBoundaryShare *
                finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator
                  β H n


end Exact3D
end StatMech
