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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part85
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_nonneg
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω := by
  classical
  unfold finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap
  exact Finset.sum_nonneg
    (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))


theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairs_sum
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ m ∈ Ω,
          ((finiteBoundaryGhostBoundaryCrossingPairs m w).card : ℝ) := by
  exact
    (finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_domain_card
      Ω v).trans
      (finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_card_le_crossingPairs_sum
        Ω)


theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairCap
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω := by
  simpa [finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap] using
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairs_sum
      Ω v


end Exact3D
end StatMech
