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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part87
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_nonneg
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
        n Ω := by
  classical
  unfold finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
  exact Finset.sum_nonneg
    (fun _ _ =>
      Finset.sum_nonneg
        (fun _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_sourceSectorMultiplicityCap
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
        n Ω := by
  classical
  unfold finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
  refine Finset.sum_le_sum ?_
  intro w _hw
  refine Finset.sum_le_sum ?_
  intro m _hm
  have hnat :=
    finiteBoundaryGhostBoundaryCrossingPairCount_le_sourceSector_card_mul_boundaryGhostMultiplicity
      m w
  have hreal :
      ((finiteBoundaryGhostBoundaryCrossingPairs m w).card : ℝ) ≤
        (((finiteBoundaryGhostSourceSector m).card *
          m (finiteBoundaryGhostBoundaryEdge n w) : ℕ) : ℝ) := by
    exact_mod_cast (by
      simpa [finiteBoundaryGhostBoundaryEdge,
        finiteBoundaryGhostBoundaryCrossingPairs_card] using hnat)
  simpa [Nat.cast_mul] using hreal


end Exact3D
end StatMech
