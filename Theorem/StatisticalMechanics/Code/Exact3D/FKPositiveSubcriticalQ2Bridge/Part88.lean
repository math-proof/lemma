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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part90
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
        n Ω := by
  classical
  unfold finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
  exact Finset.sum_nonneg
    (fun _ _ =>
      mul_nonneg
        (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
        (finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg _))


theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hΩweight :
      ∀ m, m ∈ Ω →
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠
            0) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
        n Ω ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
        n Ω := by
  classical
  calc
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
        n Ω =
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorBoundaryGhostMultiplicityCap
        n Ω :=
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_eq_sourceSectorBoundaryGhostMultiplicityCap
        Ω
    _ ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
        n Ω := by
      unfold
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorBoundaryGhostMultiplicityCap
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
      refine Finset.sum_le_sum ?_
      intro m hm
      exact
        mul_le_mul_of_nonneg_right
          (finiteBoundaryGhostSourceSector_card_le_boundaryCrossingPairCount_sum
            (β := β) (H := H) m (hΩweight m hm))
          (finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg m)


theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap_weightNonzeroCutoff
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
        n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) ≤
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
        n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) := by
  classical
  exact
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap
      (β := β) (H := H)
      (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
      (fun m hm =>
        finiteBoundaryGhostWeightNonzeroCutoff_weight_ne_zero
          (β := β) (H := H) (n := n) (Ω := Ω) hm)


theorem finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_sum_eq_image_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
    let B : Finset (FK.boxVerts 3 n) :=
      Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
    (I.image.card : ℝ) =
      ∑ v ∈ B, finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  have hmaps : ∀ d, d ∈ I.image → d.1 ∈ B := by
    intro d hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary Ω hd⟩
  calc
    (I.image.card : ℝ) =
        ∑ _d ∈ I.image, (1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    _ =
        ∑ v ∈ B, ∑ _d ∈ I.image.filter (fun d => d.1 = v), (1 : ℝ) := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := I.image) (t := B) (g := fun d => d.1)
        hmaps (fun _ => (1 : ℝ))]
    _ =
        ∑ v ∈ B, finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard, I]


end Exact3D
end StatMech
