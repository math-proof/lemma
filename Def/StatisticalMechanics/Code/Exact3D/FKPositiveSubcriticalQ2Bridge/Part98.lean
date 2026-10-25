/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part95
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
            ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
            ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n
                  (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            ∃ cap : ℝ,
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
                cap ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∃ cap : ℝ,
            (∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
                cap) ∧
            (∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v)


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∃ cap : ℝ,
            (∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
                cap) ∧
            (∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              ∃ oneBudget boundaryPairBudget emptyBoundaryBudget : ℝ,
                cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n ≤
                  oneBudget ∧
                cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v ≤
                  boundaryPairBudget ∧
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v ≤
                  emptyBoundaryBudget ∧
                oneBudget + boundaryPairBudget + emptyBoundaryBudget ≤
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v)


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let cap :=
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap
                n Ω
            ∃ oneBudget boundaryPairBudget emptyBoundaryBudget : ℝ,
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneBudget ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairBudget ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryBudget ∧
              oneBudget + boundaryPairBudget + emptyBoundaryBudget ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                  β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let cap :=
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberDecrementImageMultiplicityCap
                n Ω
            ∃ oneBudget boundaryPairBudget emptyBoundaryBudget : ℝ,
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneBudget ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairBudget ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryBudget ∧
              oneBudget + boundaryPairBudget + emptyBoundaryBudget ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                  β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let cap :=
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
                n Ω
            ∃ oneBudget boundaryPairBudget emptyBoundaryBudget : ℝ,
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneBudget ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairBudget ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryBudget ∧
              oneBudget + boundaryPairBudget + emptyBoundaryBudget ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                  β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap :=
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
                n Ωnz
            ∃ oneBudget boundaryPairBudget emptyBoundaryBudget : ℝ,
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneBudget ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairBudget ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryBudget ∧
              oneBudget + boundaryPairBudget + emptyBoundaryBudget ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                  β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap :=
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
                n Ωnz
            ∃ oneBudget boundaryPairBudget emptyBoundaryBudget : ℝ,
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneBudget ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairBudget ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryBudget ∧
              oneBudget + boundaryPairBudget + emptyBoundaryBudget ≤
                finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                  β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap :=
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
                n Ωnz
            let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
              β H n v
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              oneShare + boundaryPairShare + emptyBoundaryShare ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * D ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * D ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * D


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
          0 < finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
          let G := Sharpness.withGhost (FK.boxGraph 3 n)
          let J :=
            Sharpness.couplingIn
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (finiteBoundaryGhostOriginalSet 3 n)
          ∃ m : ↥G.edgeFinset → ℕ,
            Sharpness.sources G (Sharpness.ofEdgeFun G m) =
              ({some (IsingFK.boxOrigin 3 n), some v} :
                Finset (Option (FK.boxVerts 3 n))) ∧
            0 < Sharpness.weight G β J (Sharpness.ofEdgeFun G m)


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
          let G := Sharpness.withGhost (FK.boxGraph 3 n)
          let J :=
            Sharpness.couplingIn
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (finiteBoundaryGhostOriginalSet 3 n)
          ∃ m : ↥G.edgeFinset → ℕ,
            Sharpness.sources G (Sharpness.ofEdgeFun G m) =
              ({some (IsingFK.boxOrigin 3 n), some v} :
                Finset (Option (FK.boxVerts 3 n))) ∧
            ∀ e : ↥G.edgeFinset, 0 < m e → 0 < J e.1


def FiniteBoundaryGhostOriginalPathWitness3D : Prop :=
  ∀ᶠ n in atTop,
    ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
      ∃ p :
        (Sharpness.withGhost (FK.boxGraph 3 n)).Path
          (some (IsingFK.boxOrigin 3 n)) (some v),
        ∀ e : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset,
          0 < p.1.edges.count e.1 →
            Sharpness.edgeInside (finiteBoundaryGhostOriginalSet 3 n) e.1


end Exact3D
end StatMech
