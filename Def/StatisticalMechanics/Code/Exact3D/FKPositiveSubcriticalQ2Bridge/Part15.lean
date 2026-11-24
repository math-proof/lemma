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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part14
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
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
          (IsingFK.boxOrigin 3 n)
        ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ σ : ConfigSpace (FK.boxVerts 3 n),
          Ising.isingProb (FK.boxGraph 3 n) β 0 σ *
            (Ising.spin σ (IsingFK.boxOrigin 3 n) * Ising.spin σ v)

set_option linter.style.longLine false in


def FiniteQ2SimonFreeBoundaryIsingBoxAt
    (β : ℝ) (n : ℕ) : Prop :=
  IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
      (IsingFK.boxOrigin 3 n)
    ≤
  ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
    ∑ σ : ConfigSpace (FK.boxVerts 3 n),
      Ising.isingProb (FK.boxGraph 3 n) β 0 σ *
        (Ising.spin σ (IsingFK.boxOrigin 3 n) * Ising.spin σ v)

end Exact3D
end StatMech
