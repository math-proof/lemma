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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part14
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


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
