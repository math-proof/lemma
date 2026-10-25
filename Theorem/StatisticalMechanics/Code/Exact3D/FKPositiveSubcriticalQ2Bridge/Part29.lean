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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part30
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : finiteBoundaryGhostCollapsedTwoPointSourceData n v) :
    0 ≤ finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
  exact finiteBoundaryGhostTwoPointSourceDataWeight_nonneg hβ hH d.toSourceData


theorem finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :
    Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach
      (fun K =>
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
          ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) =
      ((finiteBoundaryGhostTwoPointSourceSector m v).card : ℝ) *
        ((β * H) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) := by
  classical
  trans
      Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach
        (fun _ =>
          (β * H) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
  · refine Finset.sum_congr rfl ?_
    intro K _hK
    rfl
  · rw [Finset.sum_const]
    rw [nsmul_eq_mul]
    rw [Finset.card_attach]


theorem
    finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight_eq_edgeCopySummand
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :
    Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach
      (fun K =>
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
          ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) =
      (β * H) *
        (((if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then
            (1 : ℝ)
          else
            0) *
          (((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)).powerset.filter
              (fun K =>
                Sharpness.RandomCurrent.sources
                  (Sharpness.FluxEdgeCopy.endsM
                    (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
                  (({some (IsingFK.boxOrigin 3 n)} :
                    Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))).card : ℝ)) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) := by
  classical
  rw [finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight
    (β := β) (H := H) m v hsrc]
  rw [if_pos hsrc]
  unfold finiteBoundaryGhostTwoPointSourceSector
  ring


theorem
    finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_mul_emptyCollapsedSum
    {β H : ℝ} {n : ℕ} (v : FK.boxVerts 3 n) :
    (∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
      if hsrc :
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then
        Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach
          (fun K =>
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
              ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩)
      else
        0)
      =
        (β * H) *
          edgeCopySourcePairEmptyCollapsedSum
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  unfold edgeCopySourcePairEmptyCollapsedSum
  rw [← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
  · rw [dif_pos hsrc]
    exact
      finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight_eq_edgeCopySummand
        (β := β) (H := H) m v hsrc
  · rw [dif_neg hsrc]
    simp [hsrc]


theorem finiteBoundaryGhostCollapsedDataWeight_fiberSummable
    {β H : ℝ} {n : ℕ} (v : FK.boxVerts 3 n) :
    Summable (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      if hsrc :
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then
        Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach
          (fun K =>
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
              ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩)
  else
        0) := by
  classical
  have hbase :=
    (edgeCopySourcePairEmptyCollapsedSummand_summable
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})).mul_left (β * H)
  refine hbase.congr (fun m => ?_)
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
  · rw [dif_pos hsrc]
    exact
      (finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight_eq_edgeCopySummand
        (β := β) (H := H) m v hsrc).symm
  · rw [dif_neg hsrc]
    simp [hsrc]


theorem finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_indicator
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (∑' K :
      {K : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m) //
        K ∈ finiteBoundaryGhostTwoPointSourceSector m v ∧
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v})},
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, K⟩)
      =
        if hsrc :
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then
          Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach
            (fun K =>
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
                ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩)
        else
          0 := by
  classical
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
  · rw [dif_pos hsrc]
    let e :
        {K : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) //
          K ∈ finiteBoundaryGhostTwoPointSourceSector m v ∧
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v})} ≃
          {K : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m) //
            K ∈ finiteBoundaryGhostTwoPointSourceSector m v} :=
      { toFun := fun K => ⟨K.1, K.2.1⟩
        invFun := fun K => ⟨K.1, ⟨K.2, hsrc⟩⟩
        left_inv := by
          intro K
          apply Subtype.ext
          rfl
        right_inv := by
          intro K
          apply Subtype.ext
          rfl }
    calc
      (∑' K :
        {K : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) //
          K ∈ finiteBoundaryGhostTwoPointSourceSector m v ∧
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v})},
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, K⟩)
          =
            ∑' K :
              {K : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m) //
                K ∈ finiteBoundaryGhostTwoPointSourceSector m v},
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
                ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩ := by
        rw [← e.tsum_eq]
        refine tsum_congr (fun K => ?_)
        simp [e]
      _ =
          Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach
            (fun K =>
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
                ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) := by
        rw [tsum_fintype]
        rfl
  · rw [dif_neg hsrc]
    have hzero :
        (fun K :
          {K : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m) //
            K ∈ finiteBoundaryGhostTwoPointSourceSector m v ∧
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})} =>
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, K⟩) =
        fun _ => 0 := by
      funext K
      exact False.elim (hsrc K.2.2)
    rw [hzero, tsum_zero]


theorem finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_summable
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H) (v : FK.boxVerts 3 n) :
    Summable (fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  rw [summable_sigma_of_nonneg (fun d =>
    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg hβ hH d)]
  constructor
  · intro m
    exact summable_of_hasFiniteSupport
      (Set.finite_univ.subset (by
        intro K _hK
        trivial))
  · refine (finiteBoundaryGhostCollapsedDataWeight_fiberSummable
      (β := β) (H := H) v).congr ?_
    intro m
    exact (finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_indicator
      (β := β) (H := H) m v).symm


theorem finiteBoundaryGhostCollapsedDataWeight_tsum_eq_fiberTsum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H) (v : FK.boxVerts 3 n) :
    (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
      =
        ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
          if hsrc :
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then
            Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach
              (fun K =>
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
                  ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩)
          else
            0 := by
  classical
  have hsum :=
    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_summable
      (β := β) (H := H) hβ hH v
  rw [Summable.tsum_sigma hsum]
  refine tsum_congr (fun m => ?_)
  exact finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_indicator
    (β := β) (H := H) m v


theorem finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H) (v : FK.boxVerts 3 n) :
    (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
      =
        (β * H) *
          edgeCopySourcePairEmptyCollapsedSum
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  rw [finiteBoundaryGhostCollapsedDataWeight_tsum_eq_fiberTsum
    (β := β) (H := H) hβ hH v]
  exact finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_mul_emptyCollapsedSum
    (β := β) (H := H) v


end Exact3D
end StatMech
