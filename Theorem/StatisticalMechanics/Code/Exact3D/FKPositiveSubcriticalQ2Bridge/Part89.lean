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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part91
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_eq_onePoint_add_boundaryPair
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v =
      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v := by
  rfl


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H) :
    0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβ hH) (mul_nonneg hβ hH)
  exact
    mul_nonneg hC
      (by
        simpa [G, J] using
          edgeCopySourcePairSum_nonneg G β J
            (finiteBoundaryGhostOnePointSource 3 n)
            (∅ : Finset (Option (FK.boxVerts 3 n))) hβ hJ)


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβ hH) (mul_nonneg hβ hH)
  exact
    mul_nonneg hC
      (by
        simpa [G, J] using
          edgeCopySourcePairSum_nonneg G β J
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
            (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
            hβ hJ)


end Exact3D
end StatMech
