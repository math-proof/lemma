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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part68
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_ends
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d) :
    Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i =
      s(some d.1, none) := by
  classical
  have hiedge : i.1 = finiteBoundaryGhostBoundaryEdge n d.1 :=
    (Finset.mem_filter.mp hi).2
  simpa [Sharpness.FluxEdgeCopy.endsM, finiteBoundaryGhostBoundaryEdge]
    using congrArg Subtype.val hiedge


theorem finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_mem_source
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
    i ∈ d.2.toSourceData.2.1 :=
  (Finset.mem_filter.mp hi).2


theorem finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_not_mem_source
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
    i ∉ d.2.toSourceData.2.1 :=
  (Finset.mem_filter.mp hi).2


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_card_le_boundaryMultiplicity
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    (finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card ≤
      d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) := by
  calc
    (finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card ≤
        (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d).card := by
      exact Finset.card_le_card (by
        intro i hi
        exact (Finset.mem_filter.mp hi).1)
    _ = d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) :=
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card d


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_card_le_boundaryMultiplicity
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    (finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card ≤
      d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) := by
  calc
    (finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card ≤
        (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d).card := by
      exact Finset.card_le_card (by
        intro i hi
        exact (Finset.mem_filter.mp hi).1)
    _ = d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) :=
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card d


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_eq_card_mul_weight
    {β H : ℝ} {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
      (((finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card :
        ℕ) : ℝ) *
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
  classical
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_eq_card_mul_weight
    {β H : ℝ} {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
      (((finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card :
        ℕ) : ℝ) *
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
  classical
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]


theorem
    finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_eq_sq_decrement_weight_of_pos
    {β H : ℝ} {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (hv : FK.boxBoundary 3 n d.1)
    (hpos :
      0 < d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1)) :
    (((d.2.toSourceData.1
        (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
      finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
      (β * H) * (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1)
              (d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let m := d.2.toSourceData.1
  let e := finiteBoundaryGhostBoundaryEdge n d.1
  have hJedge : J e.1 = H := by
    simpa [J, e] using finiteBoundaryGhostBoundaryEdge_coupling H hv
  have hdec :
      ((m e : ℝ) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) =
        (β * H) *
          Sharpness.weight G β J
            (Sharpness.ofEdgeFun G (Function.update m e (m e - 1))) := by
    simpa [hJedge] using
      (weight_ofEdgeFun_decrement G β J m e hpos)
  change
    ((m e : ℝ) *
      ((β * H) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m))) =
      (β * H) * (β * H) *
        Sharpness.weight G β J
          (Sharpness.ofEdgeFun G (Function.update m e (m e - 1)))
  calc
    ((m e : ℝ) *
      ((β * H) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m))) =
        (β * H) *
          ((m e : ℝ) *
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) := by
      ring
    _ =
        (β * H) *
          ((β * H) *
            Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (Function.update m e (m e - 1)))) := by
      rw [hdec]
    _ =
        (β * H) * (β * H) *
          Sharpness.weight G β J
            (Sharpness.ofEdgeFun G (Function.update m e (m e - 1))) := by
      ring


theorem
    finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_sq_decrement_weight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (hv : FK.boxBoundary 3 n d.1) :
    (((d.2.toSourceData.1
        (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
      finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      (β * H) * (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1)
              (d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) := by
  classical
  by_cases hpos :
      0 < d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1)
  · exact le_of_eq
      (finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_eq_sq_decrement_weight_of_pos
        (β := β) (H := H) d hv hpos)
  · let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    let m := d.2.toSourceData.1
    let e := finiteBoundaryGhostBoundaryEdge n d.1
    have hzero : m e = 0 := by
      exact Nat.eq_zero_of_not_pos (by simpa [m, e] using hpos)
    have hcoef_nonneg : 0 ≤ (β * H) * (β * H) :=
      mul_self_nonneg (β * H)
    have hweight_nonneg :
        0 ≤
          Sharpness.weight G β J
            (Sharpness.ofEdgeFun G (Function.update m e (m e - 1))) := by
      exact
        weight_ofEdgeFun_nonneg_of_nonneg G β J hβ
          (boundaryGhostCoupling_nonneg
            (FK.boxBoundary 3 n) hH (fun _ => by norm_num))
          (Function.update m e (m e - 1))
    have hrhs_nonneg :
        0 ≤
          (β * H) * (β * H) *
            Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (Function.update m e (m e - 1))) :=
      mul_nonneg hcoef_nonneg hweight_nonneg
    simpa [G, J, m, e, hzero] using hrhs_nonneg


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sq_decrement_weight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (hv : FK.boxBoundary 3 n d.1) :
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      (β * H) * (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1)
              (d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) := by
  classical
  have hsum :
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
        (((finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card :
          ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_eq_card_mul_weight
      (β := β) (H := H) d
  have hcard :
      (((finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card :
        ℕ) : ℝ) ≤
        (((d.2.toSourceData.1
          (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ)) := by
    exact_mod_cast
      finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_card_le_boundaryMultiplicity d
  have hWnonneg :
      0 ≤ finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
    finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight_nonneg hβ hH d
  calc
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
        (((finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card :
          ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := hsum
    _ ≤
        (((d.2.toSourceData.1
          (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
      mul_le_mul_of_nonneg_right hcard hWnonneg
    _ ≤
      (β * H) * (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1)
              (d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) :=
      finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_sq_decrement_weight
        hβ hH d hv


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sq_decrement_weight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (hv : FK.boxBoundary 3 n d.1) :
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      (β * H) * (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1)
              (d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) := by
  classical
  have hsum :
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
        (((finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card :
          ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_eq_card_mul_weight
      (β := β) (H := H) d
  have hcard :
      (((finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card :
        ℕ) : ℝ) ≤
        (((d.2.toSourceData.1
          (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ)) := by
    exact_mod_cast
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_card_le_boundaryMultiplicity d
  have hWnonneg :
      0 ≤ finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d :=
    finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight_nonneg hβ hH d
  calc
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
        (((finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card :
          ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := hsum
    _ ≤
        (((d.2.toSourceData.1
          (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
      mul_le_mul_of_nonneg_right hcard hWnonneg
    _ ≤
      (β * H) * (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1)
              (d.2.toSourceData.1
                (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) :=
      finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_sq_decrement_weight
        hβ hH d hv


theorem finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_source
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update d.2.toSourceData.1 i.1
          (d.2.toSourceData.1 i.1 - 1)))
      (copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1) =
      finiteBoundaryGhostOnePointSource 3 n := by
  classical
  have hitarget :
      i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d :=
    (Finset.mem_filter.mp hi).1
  exact
    finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy_from_twoPoint
      d.2.toSourceData.1 d.2.toSourceData.2.1
      (finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_mem_source
        d hi)
      (finiteBoundaryGhostTwoPointSourceData_source d.2.toSourceData)
      (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_ends d hitarget)


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_mem_sourceSector
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
    copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1 ∈
      finiteBoundaryGhostSourceSector
        (Function.update d.2.toSourceData.1 i.1
          (d.2.toSourceData.1 i.1 - 1)) := by
  rw [finiteBoundaryGhostSourceSector_mem]
  exact
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_source
      d hi


theorem finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_source
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update d.2.toSourceData.1 i.1
          (d.2.toSourceData.1 i.1 - 1)))
      (copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1) =
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1}) := by
  classical
  have hiK :
      i ∉ d.2.toSourceData.2.1 :=
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_not_mem_source
      d hi
  have htransport :=
    copyDeletePreimageDecrementErase_sources
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
      d.2.toSourceData.2.1
  rw [htransport]
  have herase :
      d.2.toSourceData.2.1.erase i = d.2.toSourceData.2.1 :=
    Finset.erase_eq_of_notMem hiK
  rw [herase]
  exact finiteBoundaryGhostTwoPointSourceData_source d.2.toSourceData


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_mem_twoPointSourceSector
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
    copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i
        d.2.toSourceData.2.1 ∈
      finiteBoundaryGhostTwoPointSourceSector
        (Function.update d.2.toSourceData.1 i.1
          (d.2.toSourceData.1 i.1 - 1)) d.1 := by
  rw [finiteBoundaryGhostTwoPointSourceSector_mem]
  exact
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_source
      d hi


end Exact3D
end StatMech
