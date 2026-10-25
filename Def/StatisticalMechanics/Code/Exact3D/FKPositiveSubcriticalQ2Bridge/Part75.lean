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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part72
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
          finiteCurrentBoundaryTwoPointSum β n


def
    FiniteQ2SimonBoundaryGhostSingletonSimonLiebComparisonPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        Sharpness.SimonLieb
          (fun a b : Option (FK.boxVerts 3 n) =>
            Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b}))
          (some (IsingFK.boxOrigin 3 n))
          (finiteBoundaryGhostOriginalSet 3 n)
          (finiteBoundaryGhostSimonWeight β H n)
          ({none} : Finset (Option (FK.boxVerts 3 n))) ∧
        (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) ≤
          finiteCurrentBoundaryTwoPointSum β n


def
    FiniteQ2SimonBoundaryGhostSingletonSimonLiebLocalizationPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        Sharpness.SimonLieb
          (fun a b : Option (FK.boxVerts 3 n) =>
            Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b}))
          (some (IsingFK.boxOrigin 3 n))
          (finiteBoundaryGhostOriginalSet 3 n)
          (finiteBoundaryGhostSimonWeight β H n)
          ({none} : Finset (Option (FK.boxVerts 3 n))) ∧
        ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
          Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (Sharpness.couplingIn
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (finiteBoundaryGhostOriginalSet 3 n))
            ({some (IsingFK.boxOrigin 3 n), some v} :
              Finset (Option (FK.boxVerts 3 n)))
            ≤
          Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
            (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v})


def
    FiniteQ2SimonBoundaryGhostSingletonSimonLiebPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 ≤ H →
        Sharpness.SimonLieb
          (fun a b : Option (FK.boxVerts 3 n) =>
            Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b}))
          (some (IsingFK.boxOrigin 3 n))
          (finiteBoundaryGhostOriginalSet 3 n)
          (finiteBoundaryGhostSimonWeight β H n)
          ({none} : Finset (Option (FK.boxVerts 3 n)))


end Exact3D
end StatMech
