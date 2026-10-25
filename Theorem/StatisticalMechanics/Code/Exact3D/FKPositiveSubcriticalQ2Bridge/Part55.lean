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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part57
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostDecrementedSourceWeightFiberSummand_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (a : finiteBoundaryGhostDecrementedSourceWeightFiber n m) :
    0 ≤ finiteBoundaryGhostDecrementedSourceWeightFiberSummand β H n m a :=
  finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg
    (β := β) (H := H) hβ hH m a.1.1 a.2.1


theorem finiteBoundaryGhostDecrementedSourceWeightSummand_eq_tsum_fiber
    (β H : ℝ) (n : ℕ)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    finiteBoundaryGhostDecrementedSourceWeightSummand β H n m =
      ∑' a : finiteBoundaryGhostDecrementedSourceWeightFiber n m,
        finiteBoundaryGhostDecrementedSourceWeightFiberSummand β H n m a := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightSummand
    finiteBoundaryGhostDecrementedSourceWeightFiberSummand
    finiteBoundaryGhostDecrementedSourceWeightFiber
  rw [tsum_fintype, Fintype.sum_sigma]
  conv_lhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro v _hv
  rw [← Finset.sum_attach]
  simpa [Finset.univ_eq_attach (finiteBoundaryGhostBoundaryCrossingPairs m v.1)]


end Exact3D
end StatMech
