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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part52
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_decremented_univ_source_ne_twoPoint
    {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))
    (hinactive : ¬ finiteBoundaryGhostFullSourceOnePoint n a.1) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
            n v a).1)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
            n v a).1)) ≠
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  intro hdec
  have hdec' :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update a.1 a.2.1.2.1 (a.1 a.2.1.2.1 - 1)))
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update a.1 a.2.1.2.1 (a.1 a.2.1.2.1 - 1)))) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
    simpa [finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData,
      finiteBoundaryGhostBoundaryCrossingPairDecrementData] using hdec
  exact hinactive
    (finiteBoundaryGhostBoundaryCrossingPairs_fullSourceOnePoint_of_decremented_univ_source
      a.1 v a.2.2 hdec')


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigma_decremented_univ_source_eq_fullSource_symmDiff
    {n : ℕ} {v : FK.boxVerts 3 n}
    (a : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
            n v a).1)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData
            n v a).1)) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)) ∆
        ({some v, none} : Finset (Option (FK.boxVerts 3 n))) := by
  simpa [finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData,
    finiteBoundaryGhostBoundaryCrossingPairDecrementData] using
    (finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source_eq_fullSource_symmDiff
      a.1 v a.2.2)


end Exact3D
end StatMech
