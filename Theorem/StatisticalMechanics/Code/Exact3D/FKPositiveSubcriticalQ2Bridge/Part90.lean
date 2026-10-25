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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part92
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v =
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
  rfl


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (v : FK.boxVerts 3 n) :
    0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  let onePoint :=
    C * edgeCopySourcePairSum G β J
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n)))
  let boundaryPair :=
    C * edgeCopySourcePairSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
      (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβ hH) (mul_nonneg hβ hH)
  have hone : 0 ≤ onePoint := by
    exact mul_nonneg hC
      (edgeCopySourcePairSum_nonneg G β J
        (finiteBoundaryGhostOnePointSource 3 n)
        (∅ : Finset (Option (FK.boxVerts 3 n))) hβ hJ)
  have hboundary : 0 ≤ boundaryPair := by
    exact mul_nonneg hC
      (edgeCopySourcePairSum_nonneg G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
        (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) hβ hJ)
  simpa [finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm,
    G, J, C, onePoint, boundaryPair] using add_nonneg hone hboundary


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (v : FK.boxVerts 3 n) :
    0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  exact
    mul_nonneg (mul_nonneg hβ hH)
      (by
        simpa [G, J] using
          edgeCopySourcePairEmptyCollapsedSum_nonneg G β J
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) hβ hJ)


end Exact3D
end StatMech
