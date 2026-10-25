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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part43
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
    (β H : ℝ) {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
    ℝ :=
  (β * H) *
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update m p.2.1 (m p.2.1 - 1)))
          (copyDeletePreimageDecrementEraseFinset
            (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then
        (1 : ℝ)
      else
        0) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update m p.2.1 (m p.2.1 - 1))))


end Exact3D
end StatMech
