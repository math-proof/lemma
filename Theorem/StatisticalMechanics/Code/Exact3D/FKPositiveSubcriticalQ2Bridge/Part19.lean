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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part20
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteCurrentBoundaryTwoPointSum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    0 ≤ finiteCurrentBoundaryTwoPointSum β n := by
  classical
  unfold finiteCurrentBoundaryTwoPointSum
  exact Finset.sum_nonneg (fun v _ =>
    finiteCurrentTwoPointRatio_nonneg 3 n hβ (IsingFK.boxOrigin 3 n) v)


theorem finiteCurrentBoundaryTwoPointSum_eq_expectationJBoundarySum
    (β : ℝ) (n : ℕ) :
    finiteCurrentBoundaryTwoPointSum β n =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
          (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
  classical
  unfold finiteCurrentBoundaryTwoPointSum
  refine Finset.sum_congr rfl ?_
  intro v _hv
  simpa [finiteTwoPointSource] using
    finiteCurrentTwoPointRatio_eq_expectationJ
      3 n β (IsingFK.boxOrigin 3 n) v


end Exact3D
end StatMech
