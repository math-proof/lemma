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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part94
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposedSourcePairBound
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω =
      finiteBoundaryGhostBoundaryFiberDecomposedSourcePairBound β H n Ω := by
  simpa [finiteBoundaryGhostBoundaryFiberDecomposedSourcePairBound] using
    finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposed β H Ω


theorem
    finiteBoundaryGhostBoundaryFiberBoundaryPairWeighted_sum_le_image_card_mul_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
    let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    let C := (β * H) * (β * H)
    let boundaryPair := fun v : FK.boxVerts 3 n =>
      C * edgeCopySourcePairSum G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
        (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
    let B : Finset (FK.boxVerts 3 n) :=
      Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
    (∑ v ∈ B,
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
        boundaryPair v) ≤
      (I.image.card : ℝ) * ∑ v ∈ B, boundaryPair v := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  let boundaryPair := fun v : FK.boxVerts 3 n =>
    C * edgeCopySourcePairSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
      (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβ hH) (mul_nonneg hβ hH)
  refine
    finset_sum_mul_le_const_mul_sum_of_le_nonneg B
      (fun v => finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v)
      boundaryPair
      (M := (I.image.card : ℝ)) ?_ ?_
  · intro v _hv
    simpa [I] using
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_image_card Ω v
  · intro v _hv
    exact mul_nonneg hC
      (edgeCopySourcePairSum_nonneg G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
        (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) hβ hJ)


theorem finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_image_card_bound
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
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
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
      (I.image.card : ℝ) *
          (onePoint + ∑ v ∈ B, boundaryPair v) +
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
  have hdecomp :
      finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω =
        (I.image.card : ℝ) * onePoint +
          (∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := by
    simpa [I, G, J, C, onePoint, boundaryPair, emptyBoundary, B] using
      finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposed β H Ω
  have hweighted :
      (∑ v ∈ B,
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
          boundaryPair v) ≤
        (I.image.card : ℝ) * ∑ v ∈ B, boundaryPair v := by
    simpa [I, G, J, C, boundaryPair, B] using
      finiteBoundaryGhostBoundaryFiberBoundaryPairWeighted_sum_le_image_card_mul_sum
        hβ hH Ω
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω =
        (I.image.card : ℝ) * onePoint +
          (∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := hdecomp
    _ ≤
        (I.image.card : ℝ) * onePoint +
          ((I.image.card : ℝ) * ∑ v ∈ B, boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := by
      linarith
    _ =
        (I.image.card : ℝ) *
            (onePoint + ∑ v ∈ B, boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := by
      ring


end Exact3D
end StatMech
