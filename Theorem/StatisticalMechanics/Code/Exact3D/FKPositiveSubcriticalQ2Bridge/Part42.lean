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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part43
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_weight
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (W : finiteBoundaryGhostTwoPointSourceData n v → ℝ) :
    Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain
      (fun a =>
        W ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) =
      Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).image
        (fun d =>
          (((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).fiber d).card :
            ℝ) * W d) :=
  FinsetFiberIndex.sum_fiber_weight
    (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v) W


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_dataWeight
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain
      (fun a =>
        finiteBoundaryGhostTwoPointSourceDataWeight β H
          ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) =
      Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).image
        (fun d =>
          (((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).fiber d).card :
            ℝ) *
            finiteBoundaryGhostTwoPointSourceDataWeight β H d) :=
  finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_weight m v
    (finiteBoundaryGhostTwoPointSourceDataWeight β H)


theorem
    finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_dataWeight_le_boundaryGhostMultiplicity_mul_image_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain
      (fun a =>
        finiteBoundaryGhostTwoPointSourceDataWeight β H
          ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a))
      ≤
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          Finset.sum
            (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).image
            (fun d => finiteBoundaryGhostTwoPointSourceDataWeight β H d) := by
  classical
  let eGhost : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset :=
    ⟨s(some v, none), by
      rw [SimpleGraph.mem_edgeFinset]
      simp [Sharpness.withGhost]⟩
  let I := finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v
  change
    Finset.sum I.domain
        (fun a => finiteBoundaryGhostTwoPointSourceDataWeight β H (I.map a)) ≤
      (m eGhost : ℝ) *
        Finset.sum I.image
          (fun d => finiteBoundaryGhostTwoPointSourceDataWeight β H d)
  refine
    FinsetFiberIndex.sum_le_const_mul_image_sum_of_fiber_card_le
      I (finiteBoundaryGhostTwoPointSourceDataWeight β H) ?_ ?_
  · intro d _hd
    have hcard :
        (I.fiber d).card ≤ m eGhost := by
      simpa [I, eGhost] using
        finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity
          m v d
    exact_mod_cast hcard
  · intro d _hd
    exact finiteBoundaryGhostTwoPointSourceDataWeight_nonneg hβ hH d


end Exact3D
end StatMech
