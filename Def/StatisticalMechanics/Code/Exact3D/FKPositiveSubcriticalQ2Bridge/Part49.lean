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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part47
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def finiteBoundaryGhostSelectedPairCutoffSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
    ∑ m ∈ Ω,
      ∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
        (if Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            finiteBoundaryGhostOnePointSource 3 n then
            (1 : ℝ)
          else
            0) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)


noncomputable def finiteBoundaryGhostDecrementedSourceWeightCutoffSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
    ∑ m ∈ Ω,
      Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
        (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
          β H m v)


noncomputable def finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) : ℝ :=
  ∑ m ∈ Ω,
    Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
      (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
        β H m v)


end Exact3D
end StatMech
