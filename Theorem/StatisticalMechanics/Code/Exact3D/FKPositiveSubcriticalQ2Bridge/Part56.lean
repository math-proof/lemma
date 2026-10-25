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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part58
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n)) :
    0 ≤ finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a :=
  finiteBoundaryGhostDecrementedSourceWeightFiberSummand_nonneg
    (β := β) (H := H) hβ hH a.1 a.2


theorem
    finiteBoundaryGhostDecrementedSourceWeightFiber_tsum_eq_boundary_pair_tsum
    (β H : ℝ) (n : ℕ)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    (∑' a : finiteBoundaryGhostDecrementedSourceWeightFiber n m,
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n ⟨m, a⟩) =
      ∑' v : {v : FK.boxVerts 3 n //
          v ∈ Finset.univ.filter (FK.boxBoundary 3 n)},
        ∑' p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v.1},
          finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m v.1 p.1 := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightSigmaSummand
    finiteBoundaryGhostDecrementedSourceWeightFiberSummand
    finiteBoundaryGhostDecrementedSourceWeightFiber
  rw [tsum_fintype, Fintype.sum_sigma]
  conv_rhs => rw [tsum_fintype]
  refine Finset.sum_congr rfl ?_
  intro v _hv
  rw [tsum_fintype]


theorem
    finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_tsum_eq_tsum_current_boundary_pair
    {β H : ℝ} {n : ℕ}
    (hsum :
      Summable (finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n)) :
    (∑' a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n),
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) =
      ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
        ∑' v : {v : FK.boxVerts 3 n //
            v ∈ Finset.univ.filter (FK.boxBoundary 3 n)},
          ∑' p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v.1},
            finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
              β H m v.1 p.1 := by
  classical
  calc
    (∑' a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n),
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a)
        =
      ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
        ∑' a : finiteBoundaryGhostDecrementedSourceWeightFiber n m,
          finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n ⟨m, a⟩ :=
      Summable.tsum_sigma hsum
    _ =
      ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
        ∑' v : {v : FK.boxVerts 3 n //
            v ∈ Finset.univ.filter (FK.boxBoundary 3 n)},
          ∑' p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v.1},
            finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
              β H m v.1 p.1 := by
      refine tsum_congr ?_
      intro m
      exact
        finiteBoundaryGhostDecrementedSourceWeightFiber_tsum_eq_boundary_pair_tsum
          β H n m


end Exact3D
end StatMech
