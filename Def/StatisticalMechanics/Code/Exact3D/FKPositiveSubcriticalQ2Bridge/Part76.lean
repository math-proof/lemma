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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part73
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def
    FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {none})
        ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
            finiteBoundaryGhostSimonWeight β H n x none


def
    FiniteQ2SimonBoundaryGhostScalarCurrentBoundPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
          ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
            finiteBoundaryGhostSimonWeight β H n x none


def
    FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource 3 n)
        ≤
          (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
            finiteBoundaryGhostSimonWeight β H n x none) *
            Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) ∅


def
    FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource 3 n)
          (∅ : Finset (Option (FK.boxVerts 3 n)))
        ≤
          (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
            finiteBoundaryGhostSimonWeight β H n x none) *
            Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (∅ : Finset (Option (FK.boxVerts 3 n)))
              (∅ : Finset (Option (FK.boxVerts 3 n)))


def
    FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource 3 n)
          (∅ : Finset (Option (FK.boxVerts 3 n)))
        ≤
          (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
            finiteBoundaryGhostSimonWeight β H n x none) *
            edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (∅ : Finset (Option (FK.boxVerts 3 n)))
              (∅ : Finset (Option (FK.boxVerts 3 n)))


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource 3 n)
        ≤
          (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
            finiteBoundaryGhostSimonWeight β H n x none) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (∅ : Finset (Option (FK.boxVerts 3 n)))


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        edgeCopySourcePairEmptyCollapsedSum
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource 3 n)
        ≤
          (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
            finiteBoundaryGhostSimonWeight β H n x none) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (∅ : Finset (Option (FK.boxVerts 3 n)))


end Exact3D
end StatMech
