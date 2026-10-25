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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part96
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_boundaryFiberImageCardCurrentDenominator
    (β H : ℝ) (n : ℕ) :
    finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n =
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator
        β H n := by
  simpa [
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator]
    using
      finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_currentSum_empty_sq
        β H n


theorem
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator_nonneg
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H) :
    0 ≤
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator
        β H n := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  have hJ : ∀ e, 0 ≤ J e := by
    dsimp [J]
    exact boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH
      (fun _ => by norm_num)
  have hboundary : 0 ≤ finiteCurrentBoundaryTwoPointSum β n :=
    finiteCurrentBoundaryTwoPointSum_nonneg hβ n
  have hempty :
      0 ≤
        Sharpness.currentSum G β J
          (∅ : Finset (Option (FK.boxVerts 3 n))) :=
    Sharpness.ssl_currentSum_nonneg G β J hβ hJ
      (∅ : Finset (Option (FK.boxVerts 3 n)))
  simpa [
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator,
    G, J] using
    mul_nonneg hboundary (mul_nonneg hempty hempty)


theorem finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_eq_tanh_mul_normalized
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hT : Real.tanh (β * H) ≠ 0) :
    finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω =
      Real.tanh (β * H) *
        finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound
          β H n Ω := by
  classical
  unfold finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound
  ring_nf
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  field_simp [hT]


theorem
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound_eq_currentBound
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound
        β H n Ω =
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
        β H n Ω := by
  classical
  unfold finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
  simp [edgeCopySourcePairSum_eq_currentSum_mul,
    edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul]


theorem finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤ finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω := by
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
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβ hH) (mul_nonneg hβ hH)
  have hcard : 0 ≤ (I.image.card : ℝ) :=
    Nat.cast_nonneg _
  have hone : 0 ≤ onePoint := by
    exact mul_nonneg hC
      (edgeCopySourcePairSum_nonneg G β J
        (finiteBoundaryGhostOnePointSource 3 n)
        (∅ : Finset (Option (FK.boxVerts 3 n))) hβ hJ)
  have hboundary : 0 ≤ ∑ v ∈ B, boundaryPair v := by
    refine Finset.sum_nonneg ?_
    intro v _hv
    exact mul_nonneg hC
      (edgeCopySourcePairSum_nonneg G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
        (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) hβ hJ)
  have hempty : 0 ≤ ∑ v ∈ B, emptyBoundary v := by
    refine Finset.sum_nonneg ?_
    intro v _hv
    exact mul_nonneg (mul_nonneg hβ hH)
      (edgeCopySourcePairEmptyCollapsedSum_nonneg G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) hβ hJ)
  simpa [finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound, I, G, J, C,
    onePoint, boundaryPair, emptyBoundary, B] using
    add_nonneg (mul_nonneg hcard (add_nonneg hone hboundary)) hempty


theorem finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_imageCardSourcePairBound
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
      finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω := by
  simpa [finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound] using
    finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_image_card_bound
      hβ hH Ω


theorem
    finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardSourcePairBound
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hbound :
      finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω ≤
        finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n) :
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
      finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
  (finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_imageCardSourcePairBound
    hβ hH Ω).trans hbound


theorem
    finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposed_le_boundaryVertexProduct
    (β H : ℝ) {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hdecomposed :
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
      (I.image.card : ℝ) * onePoint +
          (∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v ≤
        ∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) :
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
      finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
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
  have hprofile :
      finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω =
        (I.image.card : ℝ) * onePoint +
          (∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := by
    simpa [I, G, J, C, onePoint, boundaryPair, emptyBoundary, B] using
      finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposed β H Ω
  have hboundary :
      (∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) =
        finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
    rw [finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct]
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω =
        (I.image.card : ℝ) * onePoint +
          (∑ v ∈ B,
            finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
              boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := hprofile
    _ ≤
        ∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
      simpa [I, G, J, C, onePoint, boundaryPair, emptyBoundary, B] using
        hdecomposed
    _ = finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
      hboundary


theorem
    finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposedSourcePairBound
    (β H : ℝ) {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hbound :
      finiteBoundaryGhostBoundaryFiberDecomposedSourcePairBound β H n Ω ≤
        ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n =>
          FK.boxBoundary 3 n v),
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) :
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
      finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
  classical
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  have hboundary :
      (∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) =
        finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
    rw [finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct]
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω =
        finiteBoundaryGhostBoundaryFiberDecomposedSourcePairBound β H n Ω :=
      finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposedSourcePairBound
        β H n Ω
    _ ≤
        ∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
      simpa [B] using hbound
    _ = finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
      hboundary


theorem
    finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardBound_le_boundaryVertexProduct
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hbound :
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
      (I.image.card : ℝ) *
            (onePoint + ∑ v ∈ B, boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v ≤
        ∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) :
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
      finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
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
  have hprofile :
      finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
        (I.image.card : ℝ) *
            (onePoint + ∑ v ∈ B, boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := by
    simpa [I, G, J, C, onePoint, boundaryPair, emptyBoundary, B] using
      finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_image_card_bound
        hβ hH Ω
  have hboundary :
      (∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) =
        finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
    rw [finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct]
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
        (I.image.card : ℝ) *
            (onePoint + ∑ v ∈ B, boundaryPair v) +
          ∑ v ∈ B, emptyBoundary v := hprofile
    _ ≤
        ∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
      simpa [I, G, J, C, onePoint, boundaryPair, emptyBoundary, B] using
        hbound
    _ = finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
      hboundary

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω := by
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
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        (∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            (onePoint + boundaryPair v)) +
        ∑ v ∈ B, emptyBoundary v := by
      simpa [I, G, J, C, onePoint, boundaryPair, emptyBoundary, B] using
        finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairSum_add_emptyCollapsedSum_sum
          (β := β) (H := H) hβ hH Ω
    _ =
        finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω := by
      unfold finiteBoundaryGhostBoundaryFiberSourcePairProfile
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
      simp [I, G, J, C, onePoint, boundaryPair, emptyBoundary, B,
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard,
        Finset.sum_add_distrib]


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile_weightNonzeroCutoff
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n
        (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) := by
  rw [
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_eq_weightNonzeroCutoff]
  exact
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile
      (β := β) (H := H) hβ hH
      (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v := by
  classical
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
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβ hH) (mul_nonneg hβ hH)
  have hone : 0 ≤ onePoint := by
    exact mul_nonneg hC
      (edgeCopySourcePairSum_nonneg G β J
        (finiteBoundaryGhostOnePointSource 3 n)
        (∅ : Finset (Option (FK.boxVerts 3 n))) hβ hJ)
  have hboundary : 0 ≤ boundaryPair v := by
    exact mul_nonneg hC
      (edgeCopySourcePairSum_nonneg G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
        (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) hβ hJ)
  have hempty : 0 ≤ emptyBoundary v := by
    exact mul_nonneg (mul_nonneg hβ hH)
      (edgeCopySourcePairEmptyCollapsedSum_nonneg G β J
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) hβ hJ)
  have hcoef :
      0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v :=
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_nonneg Ω v
  simpa [finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile, G, J, C,
    onePoint, boundaryPair, emptyBoundary] using
    add_nonneg (mul_nonneg hcoef (add_nonneg hone hboundary)) hempty


theorem finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_le_of_boundaryFiberCard_le
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {Ω Ω' : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hcard :
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω' v) :
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω' v := by
  have hmain :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg
      (β := β) (H := H) hβ hH v
  have hmul :
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω' v *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v :=
    mul_le_mul_of_nonneg_right hcard hmain
  rw [
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty,
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty]
  exact add_le_add hmul
    (le_refl (finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v))

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_mul_main_add_empty_le_boundaryFiberSourcePairVertexProfile
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
    ((I.image.card : ℝ) *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v) ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v := by
  classical
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  have hcard :
      (I.image.card : ℝ) ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
    simpa [I] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_le_boundaryFiberCard
        Ω hv
  have hmain :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg
      (β := β) (H := H) hβ hH v
  have hmul :
      (I.image.card : ℝ) *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v :=
    mul_le_mul_of_nonneg_right hcard hmain
  change
    (I.image.card : ℝ) *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v
  rw [finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty]
  exact add_le_add hmul
    (le_refl (finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v))

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_boundaryFiberSourcePairVertexMainTerm
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {v : FK.boxVerts 3 n}
    (hv : FK.boxBoundary 3 n v)
    (d : finiteBoundaryGhostCollapsedTwoPointSourceData n v) :
    (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
  classical
  let D : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v) := ⟨v, d⟩
  have hcopy :
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies D,
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H D) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
    simpa [D, finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm] using
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_le_sourcePairSum_add
        (β := β) (H := H) hβ hH D hv
  have heq :
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies D,
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H D) =
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
    simpa [D, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight] using
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_decrementedBoundaryMultiplicity_weight
        (β := β) (H := H) D
  simpa [heq] using hcopy

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_image_card_mul_main
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
    (∑ d ∈ I.image,
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤
      (I.image.card : ℝ) *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
  classical
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  change
    (∑ d ∈ I.image,
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤
      (I.image.card : ℝ) *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  calc
    (∑ d ∈ I.image,
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤
      ∑ _d ∈ I.image,
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
        refine Finset.sum_le_sum ?_
        intro d _hd
        exact
          finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_boundaryFiberSourcePairVertexMainTerm
            (β := β) (H := H) hβ hH hvbdry d
    _ =
      (I.image.card : ℝ) *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
        rw [Finset.sum_const, nsmul_eq_mul]

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_weight_sum_le_boundaryFiberSourcePairVertexEmptyTerm
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
    (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
  classical
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  have hfinite :
      (∑ d ∈ I.image,
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
        ∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
    exact
      (finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_summable
        (β := β) (H := H) hβ hH v).sum_le_tsum I.image
        (fun d _hd =>
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg
            hβ hH d)
  have htsum :
      (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) =
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
    simpa [finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm] using
      finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum
        (β := β) (H := H) hβ hH v
  exact hfinite.trans_eq htsum

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_le_image_card_mul_main_add_empty
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
    (∑ d ∈ I.image,
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) :
          ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤
      (I.image.card : ℝ) *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
  classical
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  let W : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
  have hsplit :
      (∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
            ℕ) : ℝ) * W d)) =
        (∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) :
            ℝ) * W d)) +
        ∑ d ∈ I.image, W d := by
    calc
      (∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
            ℕ) : ℝ) * W d)) =
        ∑ d ∈ I.image,
          ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
            ℕ) : ℝ) * W d) + W d) := by
          refine Finset.sum_congr rfl ?_
          intro d _hd
          have hcast :
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
                ℕ) : ℝ)) =
                (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                  ℕ) : ℝ) + 1) := by
            norm_num
          rw [hcast]
          ring
      _ =
        (∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) :
            ℝ) * W d)) +
        ∑ d ∈ I.image, W d := by
          rw [Finset.sum_add_distrib]
  have hmain :
      (∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) :
            ℝ) * W d)) ≤
        (I.image.card : ℝ) *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
    simpa [I, W] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_image_card_mul_main
        (β := β) (H := H) hβ hH Ω hv
  have hempty :
      (∑ d ∈ I.image, W d) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
    simpa [I, W] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_weight_sum_le_boundaryFiberSourcePairVertexEmptyTerm
        (β := β) (H := H) hβ hH Ω v
  change
    (∑ d ∈ I.image,
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
          ℕ) : ℝ) * W d)) ≤
      (I.image.card : ℝ) *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  rw [hsplit]
  exact add_le_add hmain hempty


theorem finiteBoundaryGhostBoundaryFiberSourcePairProfile_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω := by
  classical
  unfold finiteBoundaryGhostBoundaryFiberSourcePairProfile
  exact Finset.sum_nonneg fun v _hv =>
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_nonneg
      (β := β) (H := H) hβ hH Ω v


end Exact3D
end StatMech
