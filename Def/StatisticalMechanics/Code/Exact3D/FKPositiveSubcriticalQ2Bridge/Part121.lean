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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part118
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ xRate : ℝ,
      Tendsto
        (fun n : ℕ =>
          -Real.log (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n) /
            (n : ℝ)) atTop (nhds xRate) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
            ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
                (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
              : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
              ≤ Real.exp (-((xRate - ε) * (n : ℝ)))


end Exact3D
end StatMech
