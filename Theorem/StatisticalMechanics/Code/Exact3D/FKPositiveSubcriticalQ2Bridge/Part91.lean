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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part93
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposed
    (β H : ℝ) {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
    let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    let C := (β * H) * (β * H)
    let onePoint :=
      C * edgeCopySourcePairSum G β J
        (finiteBoundaryGhostOnePointSource 3 n)
        (∅ : Finset (Option (FK.boxVerts 3 n)))
    let boundaryPair := fun v : FK.boxVerts 3 n =>
      C * edgeCopySourcePairSum G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
        (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
    let emptyBoundary := fun v : FK.boxVerts 3 n =>
      (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
    let B : Finset (FK.boxVerts 3 n) :=
      Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω =
      (I.image.card : ℝ) * onePoint +
        (∑ v ∈ B,
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
            boundaryPair v) +
        ∑ v ∈ B, emptyBoundary v := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  let onePoint :=
    C * edgeCopySourcePairSum G β J
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n)))
  let boundaryPair := fun v : FK.boxVerts 3 n =>
    C * edgeCopySourcePairSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
      (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
  let emptyBoundary := fun v : FK.boxVerts 3 n =>
    (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  have hcard :
      (I.image.card : ℝ) =
        ∑ v ∈ B,
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
    simpa [I, B] using
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_sum_eq_image_card Ω
  have hone :
      (I.image.card : ℝ) * onePoint =
        ∑ v ∈ B,
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
            onePoint := by
    calc
      (I.image.card : ℝ) * onePoint =
          (∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v) *
            onePoint := by
        rw [hcard]
      _ =
          ∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              onePoint := by
        rw [Finset.sum_mul]
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω =
        ∑ v ∈ B,
          (finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              (onePoint + boundaryPair v) +
            emptyBoundary v) := by
      unfold finiteBoundaryGhostBoundaryFiberSourcePairProfile
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
      simp [G, J, C, onePoint, boundaryPair, emptyBoundary, B]
    _ =
        ∑ v ∈ B,
          ((finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
                onePoint +
              finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
                boundaryPair v) +
            emptyBoundary v) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      ring
    _ =
        (∑ v ∈ B,
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
            onePoint) +
          (∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ =
        (I.image.card : ℝ) * onePoint +
          (∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := by
      rw [← hone]


end Exact3D
end StatMech
