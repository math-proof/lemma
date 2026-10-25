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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part71
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex_sum_fiber_weight
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (β * H) * (β * H) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                (Function.update d.2.toSourceData.1
                  (finiteBoundaryGhostBoundaryEdge n d.1)
                  (d.2.toSourceData.1
                    (finiteBoundaryGhostBoundaryEdge n d.1) - 1)))) =
      ∑ m' ∈ (finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex Ω).fiber m').card :
          ℝ) *
          ((β * H) * (β * H) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m')) := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex Ω
  let W :
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → ℝ :=
    fun m' =>
      (β * H) * (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m')
  have hregroup :
      Finset.sum I.domain (fun a => W (I.map a)) =
        Finset.sum I.image
          (fun m' => ((I.fiber m').card : ℝ) * W m') :=
    FinsetFiberIndex.sum_fiber_weight I W
  calc
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (β * H) * (β * H) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                (Function.update d.2.toSourceData.1
                  (finiteBoundaryGhostBoundaryEdge n d.1)
                  (d.2.toSourceData.1
                    (finiteBoundaryGhostBoundaryEdge n d.1) - 1)))) =
        Finset.sum I.domain (fun a => W (I.map a)) := by
      rw [← Finset.sum_attach]
      simp [I, W, finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex]
    _ =
        Finset.sum I.image
          (fun m' => ((I.fiber m').card : ℝ) * W m') :=
      hregroup
    _ =
      ∑ m' ∈ (finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex Ω).fiber m').card :
          ℝ) *
          ((β * H) * (β * H) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m')) := by
      simp [I, W]

set_option maxHeartbeats 800000 in


theorem finiteBoundaryGhostCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) =
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image.filter
            (fun d => d.1 = v),
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
  classical
  let I := finiteBoundaryGhostCutoffDecrementIndex Ω
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  let coeff : FK.boxVerts 3 n → ℝ :=
    fun v => (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ)
  let W :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v) → ℝ :=
    finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H
  have hmaps : ∀ d, d ∈ I.image → d.1 ∈ B := by
    intro d hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        finiteBoundaryGhostCutoffDecrementIndex_image_fst_boundary Ω hd⟩
  change
    (∑ d ∈ I.image, coeff d.1 * W d) =
      ∑ v ∈ B, coeff v *
        (∑ d ∈ I.image.filter (fun d => d.1 = v), W d)
  calc
    (∑ d ∈ I.image, coeff d.1 * W d) =
        ∑ v ∈ B,
          ∑ d ∈ I.image.filter (fun d => d.1 = v), coeff d.1 * W d := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := I.image) (t := B) (g := fun d => d.1)
        hmaps (fun d => coeff d.1 * W d)]
    _ =
        ∑ v ∈ B, coeff v *
          (∑ d ∈ I.image.filter (fun d => d.1 = v), W d) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      have hinner :
          (∑ d ∈ I.image.filter (fun d => d.1 = v), coeff d.1 * W d) =
            ∑ d ∈ I.image.filter (fun d => d.1 = v), coeff v * W d := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        exact congrArg (fun u => coeff u * W d) (Finset.mem_filter.mp hd).2
      rw [hinner]
      rw [← Finset.mul_sum]

set_option maxHeartbeats 800000 in


theorem finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.filter
            (fun d => d.1 = v),
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  let coeff : FK.boxVerts 3 n → ℝ :=
    fun v => (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ)
  let W :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostCollapsedTwoPointSourceData n v) → ℝ :=
    finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H
  have hmaps : ∀ d, d ∈ I.image → d.1 ∈ B := by
    intro d hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary Ω hd⟩
  change
    (∑ d ∈ I.image, coeff d.1 * W d) =
      ∑ v ∈ B, coeff v *
        (∑ d ∈ I.image.filter (fun d => d.1 = v), W d)
  calc
    (∑ d ∈ I.image, coeff d.1 * W d) =
        ∑ v ∈ B,
          ∑ d ∈ I.image.filter (fun d => d.1 = v), coeff d.1 * W d := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := I.image) (t := B) (g := fun d => d.1)
        hmaps (fun d => coeff d.1 * W d)]
    _ =
        ∑ v ∈ B, coeff v *
          (∑ d ∈ I.image.filter (fun d => d.1 = v), W d) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      have hinner :
          (∑ d ∈ I.image.filter (fun d => d.1 = v), coeff d.1 * W d) =
            ∑ d ∈ I.image.filter (fun d => d.1 = v), coeff v * W d := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        exact congrArg (fun u => coeff u * W d) (Finset.mem_filter.mp hd).2
      rw [hinner]
      rw [← Finset.mul_sum]

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryImage_weight_sum_le_tsum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.filter
        (fun d : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostCollapsedTwoPointSourceData n v) => d.1 = v),
      finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let S : Finset (Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :=
    I.image.filter (fun d => d.1 = v)
  let e : S ↪ finiteBoundaryGhostCollapsedTwoPointSourceData n v :=
    { toFun := fun d => by
        exact (Finset.mem_filter.mp d.2).2 ▸ d.1.2
      inj' := by
        intro x y hxy
        apply Subtype.ext
        rcases x with ⟨dx, hdxS⟩
        rcases y with ⟨dy, hdyS⟩
        rcases dx with ⟨vx, dx⟩
        rcases dy with ⟨vy, dy⟩
        dsimp at hxy
        have hvx : vx = v := (Finset.mem_filter.mp hdxS).2
        have hvy : vy = v := (Finset.mem_filter.mp hdyS).2
        subst vx
        subst vy
        simpa using hxy }
  have hsum_map :
      (∑ x ∈ S.attach.map e,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H x) =
        ∑ x ∈ S.attach,
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H (e x) := by
    exact Finset.sum_map S.attach e
      (finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H)
  have hsum_eq :
      (∑ d ∈ S,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
        ∑ x ∈ S.attach.map e,
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H x := by
    calc
      (∑ d ∈ S,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
          ∑ x ∈ S.attach,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H x.1 := by
        rw [Finset.sum_attach]
      _ = ∑ x ∈ S.attach,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H (e x) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        rcases x with ⟨dx, hdxS⟩
        rcases dx with ⟨vx, dx⟩
        dsimp [e, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight]
        have hvx : vx = v := (Finset.mem_filter.mp hdxS).2
        subst vx
        rfl
      _ = ∑ x ∈ S.attach.map e,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H x := hsum_map.symm
  rw [hsum_eq]
  exact (finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_summable
    (β := β) (H := H) hβ hH v).sum_le_tsum
    (S.attach.map e)
    (fun d _hd => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg hβ hH d)

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_weight_sum_le_emptyCollapsedSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (β * H) *
          edgeCopySourcePairEmptyCollapsedSum
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  let W :
      Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostCollapsedTwoPointSourceData n v) → ℝ :=
    finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H
  have hmaps : ∀ d, d ∈ I.image → d.1 ∈ B := by
    intro d hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary Ω hd⟩
  calc
    (∑ d ∈ I.image, W d) =
        ∑ v ∈ B, ∑ d ∈ I.image.filter (fun d => d.1 = v), W d := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := I.image) (t := B) (g := fun d => d.1)
        hmaps W]
    _ ≤
        ∑ v ∈ B,
          ∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
      refine Finset.sum_le_sum ?_
      intro v _hv
      exact
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryImage_weight_sum_le_tsum
          (β := β) (H := H) hβ hH Ω v
    _ =
        ∑ v ∈ B,
          (β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      rw [finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum
        (β := β) (H := H) hβ hH v]

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_tsum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  calc
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.filter
            (fun d => d.1 = v),
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum
        Ω
    _ ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
      refine Finset.sum_le_sum ?_
      intro v _hv
      have hcoeff_nonneg :
          0 ≤ (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le
          (∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v))
      exact mul_le_mul_of_nonneg_left
        (finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryImage_weight_sum_le_tsum
          (β := β) (H := H) hβ hH Ω v)
        hcoeff_nonneg

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_emptyCollapsedSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  calc
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_tsum_sum
        hβ hH Ω
    _ =
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      rw [finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum
        (β := β) (H := H) hβ hH v]

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_tsum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  calc
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum
        hβ hH Ω
    _ ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_tsum_sum
        hβ hH Ω

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_emptyCollapsedSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  calc
    (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum
        hβ hH Ω
    _ ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_emptyCollapsedSum_sum
        hβ hH Ω


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_sum_eq_image_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain
      (fun a =>
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H
          ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a)) =
      ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
  FinsetFiberIndex.sum_fiber_weight
    (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω)
    (finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H)

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementIndex_image_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m)
        ≤ finiteBoundaryGhostSelectedPairCutoffSum β H n Ω :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_selectedPairCutoffSum
        (β := β) (H := H) hβ hH Ω
    _ ≤
        Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain
          (fun a =>
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H
              ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a)) :=
      finiteBoundaryGhostSelectedPairCutoffSum_le_collapsedCutoffDecrementIndex_domain_sum
        (β := β) (H := H) hβ hH Ω
    _ =
        ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
          (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_sum_eq_image_sum
        (β := β) (H := H) Ω

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_succ_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
        (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
          (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementIndex_image_sum
        hβ hH Ω
    _ ≤
        ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
          (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
        hβ hH Ω

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_weight_sum_add_emptyCollapsedSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) +
      Finset.sum
        (Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v))
        (fun v =>
          (β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
          (((d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_succ_weight_sum
        hβ hH Ω
    _ =
        (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) +
        ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum
        (β := β) (H := H) (n := n) Ω
    _ ≤
        (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) +
        ∑ v ∈ Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
          (β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
      exact add_le_add_right
        (finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_weight_sum_le_emptyCollapsedSum_sum
          (β := β) (H := H) hβ hH Ω)
        _

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_regroupedSourcePairSum_add_emptyCollapsedSum_sum
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
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ((((I.image.card : ℕ) : ℝ) * onePoint) +
        ∑ v ∈ Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v) +
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        emptyBoundary v := by
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
  have htarget :
      Finset.sum I.image
          (fun d =>
            (((d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
              finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) ≤
        (((I.image.card : ℕ) : ℝ) * onePoint) +
          ∑ v ∈ B,
            (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
              boundaryPair v := by
    simpa [I, G, J, C, onePoint, boundaryPair, B] using
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_regrouped_sourcePairSum
        hβ hH Ω
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        Finset.sum I.image
          (fun d =>
            (((d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
              finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) +
        ∑ v ∈ B, emptyBoundary v := by
      simpa [I, G, J, B, emptyBoundary] using
        finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_weight_sum_add_emptyCollapsedSum_sum
          hβ hH Ω
    _ ≤
        ((((I.image.card : ℕ) : ℝ) * onePoint) +
          ∑ v ∈ B,
            (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
              boundaryPair v) +
        ∑ v ∈ B, emptyBoundary v :=
      add_le_add_left htarget _

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_regroupedSourcePairSum_eq_boundaryFiberSourcePairSum
    {β H : ℝ} {n : ℕ}
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
    let B : Finset (FK.boxVerts 3 n) :=
      Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
    (((I.image.card : ℕ) : ℝ) * onePoint) +
        ∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v =
      ∑ v ∈ B,
        (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
          (onePoint + boundaryPair v) := by
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
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  have hmaps : ∀ d, d ∈ I.image → d.1 ∈ B := by
    intro d hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary Ω hd⟩
  have hone :
      (((I.image.card : ℕ) : ℝ) * onePoint) =
        ∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            onePoint := by
    calc
      (((I.image.card : ℕ) : ℝ) * onePoint) =
          Finset.sum I.image (fun _ => onePoint) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ =
          ∑ v ∈ B,
            ∑ _d ∈ I.image.filter (fun d => d.1 = v), onePoint := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := I.image) (t := B) (g := fun d => d.1)
          hmaps (fun _ => onePoint)]
      _ =
          ∑ v ∈ B,
            (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
              onePoint := by
        refine Finset.sum_congr rfl ?_
        intro v _hv
        rw [Finset.sum_const, nsmul_eq_mul]
  change
    (((I.image.card : ℕ) : ℝ) * onePoint) +
        ∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v =
      ∑ v ∈ B,
        (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
          (onePoint + boundaryPair v)
  calc
    (((I.image.card : ℕ) : ℝ) * onePoint) +
        ∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v =
      (∑ v ∈ B,
        (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
          onePoint) +
        ∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v := by
        rw [hone]
    _ =
      ∑ v ∈ B,
        ((((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
          onePoint +
        (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
          boundaryPair v) := by
        rw [← Finset.sum_add_distrib]
    _ =
      ∑ v ∈ B,
        (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
          (onePoint + boundaryPair v) := by
        refine Finset.sum_congr rfl ?_
        intro v _hv
        ring

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairSum_add_emptyCollapsedSum_sum
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
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      (∑ v ∈ B,
        (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
          (onePoint + boundaryPair v)) +
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
  have hsource :
      (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        ((((I.image.card : ℕ) : ℝ) * onePoint) +
          ∑ v ∈ B,
            (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
              boundaryPair v) +
        ∑ v ∈ B, emptyBoundary v := by
    simpa [I, G, J, C, onePoint, boundaryPair, emptyBoundary, B] using
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_regroupedSourcePairSum_add_emptyCollapsedSum_sum
        hβ hH Ω
  have hregroup :
      ((((I.image.card : ℕ) : ℝ) * onePoint) +
          ∑ v ∈ B,
            (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
              boundaryPair v) =
        ∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            (onePoint + boundaryPair v) := by
    simpa [I, G, J, C, onePoint, boundaryPair, B] using
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_regroupedSourcePairSum_eq_boundaryFiberSourcePairSum
        (β := β) (H := H) Ω
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        ((((I.image.card : ℕ) : ℝ) * onePoint) +
          ∑ v ∈ B,
            (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
              boundaryPair v) +
        ∑ v ∈ B, emptyBoundary v :=
      hsource
    _ =
        (∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            (onePoint + boundaryPair v)) +
        ∑ v ∈ B, emptyBoundary v := by
      rw [hregroup]

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_sq_decrement_weight_sum_add_emptyCollapsedSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (β * H) * (β * H) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                (Function.update d.2.toSourceData.1
                  (finiteBoundaryGhostBoundaryEdge n d.1)
                  (d.2.toSourceData.1
                    (finiteBoundaryGhostBoundaryEdge n d.1) - 1)))) +
      Finset.sum
        (Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v))
        (fun v =>
          (β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
          (fun d =>
            (((d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
              finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) +
        Finset.sum
          (Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v))
          (fun v =>
            (β * H) *
              edgeCopySourcePairEmptyCollapsedSum
                (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (({some (IsingFK.boxOrigin 3 n)} :
                  Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_weight_sum_add_emptyCollapsedSum_sum
        hβ hH Ω
    _ ≤
        Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
          (fun d =>
            (β * H) * (β * H) *
              Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                  (Function.update d.2.toSourceData.1
                    (finiteBoundaryGhostBoundaryEdge n d.1)
                    (d.2.toSourceData.1
                      (finiteBoundaryGhostBoundaryEdge n d.1) - 1)))) +
        Finset.sum
          (Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v))
          (fun v =>
            (β * H) *
              edgeCopySourcePairEmptyCollapsedSum
                (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (({some (IsingFK.boxOrigin 3 n)} :
                  Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
      exact add_le_add_left
        (finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sq_decrement_weight_sum
          (β := β) (H := H) hβ hH Ω)
        _

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffBoundaryMultiplicity_emptyCollapsedSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image,
          (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementIndex_image_sum
        hβ hH Ω
    _ ≤
        ∑ v ∈ Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
          (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
            ((β * H) *
              edgeCopySourcePairEmptyCollapsedSum
                (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (({some (IsingFK.boxOrigin 3 n)} :
                  Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :=
      finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_emptyCollapsedSum_sum
        hβ hH Ω


theorem
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_domain_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω =
      Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).domain
        (fun a =>
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H
            ((finiteBoundaryGhostCutoffDecrementIndex Ω).map a)) := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightCutoffSum
    finiteBoundaryGhostCutoffDecrementIndex
    finiteBoundaryGhostSigmaTwoPointSourceDataWeight
  rw [Finset.sum_sigma]
  conv_lhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro v _hv
  rw [Finset.sum_sigma]
  conv_lhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  simpa [finiteBoundaryGhostBoundaryCrossingPairDecrementIndex] using
    finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeightSum_eq_indexDomain
      (β := β) (H := H) m.1 v.1


theorem
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_image_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω =
      ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
  calc
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω =
        Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).domain
          (fun a =>
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H
              ((finiteBoundaryGhostCutoffDecrementIndex Ω).map a)) :=
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_domain_sum
        (β := β) (H := H) Ω
    _ =
        ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
          (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d :=
      FinsetFiberIndex.sum_fiber_weight
        (finiteBoundaryGhostCutoffDecrementIndex Ω)
        (finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H)


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementIndex_image_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m)
      ≤ finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_decrementedSourceWeightCutoffSum
        (β := β) (H := H) hβ hH Ω
    _ =
        ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
          (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_image_sum
        (β := β) (H := H) Ω

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementedBoundaryMultiplicity_succ_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
          (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementIndex_image_sum
        hβ hH Ω
    _ ≤
        ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
          (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
        hβ hH Ω

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
          (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementIndex_image_sum
        hβ hH Ω
    _ ≤
        ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
          (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum
        hβ hH Ω

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_boundary_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
        (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
          (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image.filter
            (fun d => d.1 = v),
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image,
          (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_weight_sum
        hβ hH Ω
    _ =
        ∑ v ∈ Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
          (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) *
            (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image.filter
              (fun d => d.1 = v),
              finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum
        Ω


theorem singleton_symmDiff_card_even
    {V : Type*} [DecidableEq V] (x y : V) :
    Even ((({x} : Finset V) ∆ {y}).card) := by
  classical
  by_cases h : x = y
  · subst y
    simp
  · have hset : (({x} : Finset V) ∆ {y}) = {x, y} := by
      ext z
      simp only [Finset.mem_symmDiff, Finset.mem_singleton,
        Finset.mem_insert]
      constructor
      · rintro (⟨hzx, _hzy⟩ | ⟨hzy, _hzx⟩)
        · exact Or.inl hzx
        · exact Or.inr hzy
      · intro hz
        rcases hz with hzx | hzy
        · exact Or.inl
            ⟨hzx, by intro hzy; exact h (hzx.symm.trans hzy)⟩
        · exact Or.inr
            ⟨hzy, by intro hzx; exact h (hzx.symm.trans hzy)⟩
    rw [hset]
    simp [h]


theorem finiteBoundaryGhostOriginalSet_edgeInside_map_some
    (d n : ℕ) (e : Sym2 (FK.boxVerts d n)) :
    Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n)
      (Sym2.map some e) := by
  classical
  intro z hz
  induction e with
  | h x y =>
      rw [Sym2.map_mk] at hz
      rcases z with _ | w
      · simp at hz
      · simp [finiteBoundaryGhostOriginalSet]


theorem finiteBoundaryGhostOriginalSet_not_edgeInside_some_none
    (d n : ℕ) (x : FK.boxVerts d n) :
    ¬ Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n)
      s(some x, none) := by
  classical
  intro h
  exact none_not_mem_finiteBoundaryGhostOriginalSet d n (h none (by simp))

@[simp] theorem finiteBoundaryGhostLocalizedCoupling_map_some
    (d n : ℕ) (H : ℝ) (e : Sym2 (FK.boxVerts d n)) :
    Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet d n)
        (Sym2.map some e) = 1 := by
  classical
  unfold Sharpness.couplingIn
  rw [if_pos (finiteBoundaryGhostOriginalSet_edgeInside_map_some d n e)]
  induction e with
  | h x y =>
      simp [Sym2.map_mk]

@[simp] theorem finiteBoundaryGhostLocalizedCoupling_some_none
    (d n : ℕ) (H : ℝ) (x : FK.boxVerts d n) :
    Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet d n)
        s(some x, none) = 0 := by
  classical
  unfold Sharpness.couplingIn
  simp [finiteBoundaryGhostOriginalSet_not_edgeInside_some_none]


theorem finiteBoundaryGhostLocalizedCoupling_pos_of_edgeInside
    (d n : ℕ) (H : ℝ) {e : Sym2 (Option (FK.boxVerts d n))}
    (he : Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n) e) :
    0 <
      Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet d n) e := by
  classical
  unfold Sharpness.couplingIn
  rw [if_pos he]
  induction e with
  | h a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · exact False.elim
          (none_not_mem_finiteBoundaryGhostOriginalSet d n (he none (by simp)))
      · exact False.elim
          (none_not_mem_finiteBoundaryGhostOriginalSet d n (he none (by simp)))
      · exact False.elim
          (none_not_mem_finiteBoundaryGhostOriginalSet d n (he none (by simp)))
      · simp [boundaryGhostCoupling]


theorem finiteBoundaryGhostLocalized_bondSum_eq_original
    (d n : ℕ) (H : ℝ) (s : ConfigSpace (Option (FK.boxVerts d n))) :
    (∑ e ∈ (Sharpness.withGhost (FK.boxGraph d n)).edgeFinset,
        Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet d n) e *
          Ising.bond s e) =
      ∑ e ∈ (FK.boxGraph d n).edgeFinset,
        (fun _ : Sym2 (FK.boxVerts d n) => (1 : ℝ)) e *
          Ising.bond (fun x => s (some x)) e := by
  classical
  rw [Sharpness.FieldGhostDict.withGhost_edgeFinset_eq,
    Finset.sum_union (Sharpness.FieldGhostDict.disjoint_orig_ghost
      (FK.boxGraph d n))]
  rw [show
      (∑ e ∈ Sharpness.FieldGhostDict.ghostEdges (FK.boxVerts d n),
        Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet d n) e *
          Ising.bond s e) = 0 from ?_]
  · rw [add_zero]
    rw [Sharpness.FieldGhostDict.origEdges, Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro e _he
      simp [Sharpness.FieldGhostDict.bond_map_some]
    · intro a _ha b _hb hab
      exact Sym2.map.injective (Option.some_injective (FK.boxVerts d n)) hab
  · rw [Sharpness.FieldGhostDict.ghostEdges, Finset.sum_image]
    · exact Finset.sum_eq_zero fun x _hx => by
        simp
    · intro a _ha b _hb hab
      rw [Sym2.eq_iff] at hab
      rcases hab with ⟨h1, _h2⟩ | ⟨_h1, h2⟩
      · exact Option.some_injective (FK.boxVerts d n) h1
      · exact absurd h2 (by simp)


theorem finiteBoundaryGhostLocalizedCoupling_eq_ghostCoupling_zero
    (d n : ℕ) (β H : ℝ) :
    Sharpness.couplingIn
      (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
      (finiteBoundaryGhostOriginalSet d n)
    =
    Sharpness.FieldGhostDict.ghostCoupling (0 : ℝ) β (fun _ => 1) := by
  classical
  funext e
  induction e with
  | h a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [Sharpness.couplingIn,
          Sharpness.FieldGhostDict.ghostCoupling]
      · have hnot :
            ¬ Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n)
              s(none, some y) := by
          intro h
          exact none_not_mem_finiteBoundaryGhostOriginalSet d n
            (h none (by simp))
        simp [Sharpness.couplingIn, hnot,
          Sharpness.FieldGhostDict.ghostCoupling]
      · have hnot :
            ¬ Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n)
              s(some x, none) :=
          finiteBoundaryGhostOriginalSet_not_edgeInside_some_none d n x
        simp [Sharpness.couplingIn, hnot,
          Sharpness.FieldGhostDict.ghostCoupling]
      · have hinside :
            Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n)
              s(some x, some y) := by
          intro z hz
          rcases z with _ | w
          · simp at hz
          · simp [finiteBoundaryGhostOriginalSet]
        simp [Sharpness.couplingIn, hinside,
          Sharpness.FieldGhostDict.ghostCoupling]


theorem finiteBoundaryGhostLocalizedExpectation_symmDiff_eq_boxExpectation
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet 3 n))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
    =
    Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
      (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆
        {v}) := by
  classical
  let A : Finset (FK.boxVerts 3 n) :=
    ({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}
  have hAeven : Even A.card := by
    dsimp [A]
    exact singleton_symmDiff_card_even (IsingFK.boxOrigin 3 n) v
  have hmap :
      A.map Sharpness.FieldGhostDict.someEmb =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
    dsimp [A]
    rw [Sharpness.FieldGhostDict.map_symmDiff']
    simp [Sharpness.FieldGhostDict.someEmb]
  rw [finiteBoundaryGhostLocalizedCoupling_eq_ghostCoupling_zero]
  rw [← hmap]
  rw [Sharpness.FieldGhostDict.fgd_expectationJ_ghost_eq
    (FK.boxGraph 3 n) β (0 : ℝ) A hAeven]
  rw [← Sharpness.expectationJ_one_eq_isingExpectation
    (FK.boxGraph 3 n) β A]


theorem finiteBoundaryGhostLocalizedExpectation_pair_eq_boxExpectation
    (β H : ℝ) (n : ℕ) {v : FK.boxVerts 3 n}
    (hv : IsingFK.boxOrigin 3 n ≠ v) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet 3 n))
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n)))
    =
    Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
      (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆
        {v}) := by
  classical
  have hpair :
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n))) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_symmDiff]
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact Or.inl
          ⟨hz, by
            intro hzv
            exact hv (Option.some.inj (hz.symm.trans hzv))⟩
      · exact Or.inr
          ⟨hz, by
            intro hzo
            exact hv (Option.some.inj (hzo.symm.trans hz))⟩
    · rintro (⟨hzo, _hzv⟩ | ⟨hzv, _hzo⟩)
      · exact Or.inl hzo
      · exact Or.inr hzv
  rw [hpair]
  exact finiteBoundaryGhostLocalizedExpectation_symmDiff_eq_boxExpectation
    β H n v


theorem boxOrigin_not_boxBoundary (d n : ℕ) :
    ¬ FK.boxBoundary d n (IsingFK.boxOrigin d n) := by
  rw [FK.boxBoundary, Lattice.mem_vertexBoundary]
  exact fun h => h.2 (IsingFK.origin_mem_box_boxVerts d (n - 1))


theorem boxOrigin_ne_of_boxBoundary
    (d n : ℕ) {v : FK.boxVerts d n} (hv : FK.boxBoundary d n v) :
    IsingFK.boxOrigin d n ≠ v := by
  intro h
  exact boxOrigin_not_boxBoundary d n (h ▸ hv)


theorem finiteBoundaryGhostLocalizedExpectation_boundary_eq_boxExpectation
    (β H : ℝ) (n : ℕ) {v : FK.boxVerts 3 n}
    (hv : FK.boxBoundary 3 n v) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet 3 n))
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n)))
    =
    Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
      (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆
        {v}) :=
  finiteBoundaryGhostLocalizedExpectation_pair_eq_boxExpectation
    β H n (boxOrigin_ne_of_boxBoundary 3 n hv)


theorem finiteBoundaryGhostLocalizedExpectation_boundary_le_boxExpectation
    (β H : ℝ) (n : ℕ) {v : FK.boxVerts 3 n}
    (hv : FK.boxBoundary 3 n v) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet 3 n))
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n)))
      ≤
    Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
      (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆
        {v}) := by
  exact le_of_eq
    (finiteBoundaryGhostLocalizedExpectation_boundary_eq_boxExpectation
      β H n hv)


theorem finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum
    (β H : ℝ) (n : ℕ)
    (hbdry_ne : ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
      IsingFK.boxOrigin 3 n ≠ v) :
    (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
      Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (Sharpness.couplingIn
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOriginalSet 3 n))
        ({some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n)))) =
      finiteCurrentBoundaryTwoPointSum β n := by
  classical
  rw [finiteCurrentBoundaryTwoPointSum_eq_expectationJBoundarySum]
  refine Finset.sum_congr rfl ?_
  intro v hv
  rw [finiteBoundaryGhostLocalizedExpectation_pair_eq_boxExpectation
    β H n (hbdry_ne v (Finset.mem_filter.mp hv).2)]


theorem finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum_of_boxGeometry
    (β H : ℝ) (n : ℕ) :
    (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
      Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (Sharpness.couplingIn
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOriginalSet 3 n))
        ({some (IsingFK.boxOrigin 3 n), some v} :
          Finset (Option (FK.boxVerts 3 n)))) =
      finiteCurrentBoundaryTwoPointSum β n :=
  finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum
    β H n (fun _ hv => boxOrigin_ne_of_boxBoundary 3 n hv)


end Exact3D
end StatMech
