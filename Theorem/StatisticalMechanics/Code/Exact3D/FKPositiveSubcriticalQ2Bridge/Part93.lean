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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part95
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound_eq_components
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
        β H n Ω =
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent
          β H n Ω +
        finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent
          β H n Ω +
        finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent
          β H n Ω := by
  classical
  unfold finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent
  ring


theorem
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 < β) (hH : 0 < H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent
        β H n Ω := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let C := (β * H) * (β * H)
  have hβnonneg : 0 ≤ β := le_of_lt hβ
  have hHnonneg : 0 ≤ H := le_of_lt hH
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hHnonneg
      (fun _ => by norm_num)
  have hT : 0 ≤ T := le_of_lt (real_tanh_pos_of_pos (mul_pos hβ hH))
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβnonneg hHnonneg)
      (mul_nonneg hβnonneg hHnonneg)
  have hcoef : 0 ≤ (I.image.card : ℝ) := Nat.cast_nonneg _
  have hratio : 0 ≤ C / T := div_nonneg hC hT
  have hcur :
      0 ≤
        Sharpness.currentSum G β J (finiteBoundaryGhostOnePointSource 3 n) *
          Sharpness.currentSum G β J (∅ : Finset (Option (FK.boxVerts 3 n))) :=
    mul_nonneg
      (Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ
        (finiteBoundaryGhostOnePointSource 3 n))
      (Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ
        (∅ : Finset (Option (FK.boxVerts 3 n))))
  simpa [
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent,
    I, G, J, T, C] using
    mul_nonneg hcoef (mul_nonneg hratio hcur)


theorem
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 < β) (hH : 0 < H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent
        β H n Ω := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let C := (β * H) * (β * H)
  let boundaryPair := fun v : FK.boxVerts 3 n =>
    (C / T) *
      (Sharpness.currentSum G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
        Sharpness.currentSum G β J
          (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}))
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  have hβnonneg : 0 ≤ β := le_of_lt hβ
  have hHnonneg : 0 ≤ H := le_of_lt hH
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hHnonneg
      (fun _ => by norm_num)
  have hT : 0 ≤ T := le_of_lt (real_tanh_pos_of_pos (mul_pos hβ hH))
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hβnonneg hHnonneg)
      (mul_nonneg hβnonneg hHnonneg)
  have hratio : 0 ≤ C / T := div_nonneg hC hT
  have hcoef : 0 ≤ (I.image.card : ℝ) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ v ∈ B, boundaryPair v := by
    refine Finset.sum_nonneg ?_
    intro v _hv
    exact mul_nonneg hratio
      (mul_nonneg
        (Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
        (Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ
          (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})))
  simpa [
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent,
    I, G, J, T, C, boundaryPair, B] using
    mul_nonneg hcoef hsum


theorem
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 < β) (hH : 0 < H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent
        β H n Ω := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let emptyBoundary := fun v : FK.boxVerts 3 n =>
    ((β * H) / T) *
      (Sharpness.currentSum G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
        Sharpness.currentSum G β J (∅ : Finset (Option (FK.boxVerts 3 n))))
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  have hβnonneg : 0 ≤ β := le_of_lt hβ
  have hHnonneg : 0 ≤ H := le_of_lt hH
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hHnonneg
      (fun _ => by norm_num)
  have hT : 0 ≤ T := le_of_lt (real_tanh_pos_of_pos (mul_pos hβ hH))
  have hβH : 0 ≤ β * H := mul_nonneg hβnonneg hHnonneg
  have hratio : 0 ≤ (β * H) / T := div_nonneg hβH hT
  have hsum : 0 ≤ ∑ v ∈ B, emptyBoundary v := by
    refine Finset.sum_nonneg ?_
    intro v _hv
    exact mul_nonneg hratio
      (mul_nonneg
        (Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
        (Sharpness.ssl_currentSum_nonneg G β J hβnonneg hJ
          (∅ : Finset (Option (FK.boxVerts 3 n)))))
  simpa [
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent,
    G, J, T, emptyBoundary, B] using hsum


end Exact3D
end StatMech
