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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part70
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_sq_decrement_weight_le_sourcePairSummand
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
    let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    let m' :=
      Function.update d.2.toSourceData.1 i.1
        (d.2.toSourceData.1 i.1 - 1)
    (β * H) * (β * H) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m') ≤
      (β * H) * (β * H) *
        edgeCopySourcePairSummand G β J
          (finiteBoundaryGhostOnePointSource 3 n)
          (∅ : Finset (Option (FK.boxVerts 3 n))) m' := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let m' :=
    Function.update d.2.toSourceData.1 i.1
      (d.2.toSourceData.1 i.1 - 1)
  let D :=
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_sourcePairData
      d i hi
  have hD_nonneg :
      0 ≤ edgeCopySourcePairDataWeight G β J D := by
    dsimp [D, edgeCopySourcePairDataWeight, G, J, m']
    exact
      weight_ofEdgeFun_nonneg_of_nonneg G β J hβ
        (boundaryGhostCoupling_nonneg
          (FK.boxBoundary 3 n) hH (fun _ => by norm_num))
        m'
  have hleD :=
    edgeCopySourcePairDataWeight_le_summand
      G β J D hD_nonneg
  have hle :
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m') ≤
        edgeCopySourcePairSummand G β J
          (finiteBoundaryGhostOnePointSource 3 n)
          (∅ : Finset (Option (FK.boxVerts 3 n))) m' := by
    simpa [D, edgeCopySourcePairDataWeight, G, J, m'] using hleD
  have hcoef_nonneg : 0 ≤ (β * H) * (β * H) :=
    mul_self_nonneg (β * H)
  exact mul_le_mul_of_nonneg_left hle hcoef_nonneg


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_sq_decrement_weight_le_sourcePairSummand
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
    (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
    let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    let m' :=
      Function.update d.2.toSourceData.1 i.1
        (d.2.toSourceData.1 i.1 - 1)
    (β * H) * (β * H) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m') ≤
      (β * H) * (β * H) *
        edgeCopySourcePairSummand G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
          (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m' := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let m' :=
    Function.update d.2.toSourceData.1 i.1
      (d.2.toSourceData.1 i.1 - 1)
  let D :=
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_sourcePairData
      d i hi
  have hD_nonneg :
      0 ≤ edgeCopySourcePairDataWeight G β J D := by
    dsimp [D, edgeCopySourcePairDataWeight, G, J, m']
    exact
      weight_ofEdgeFun_nonneg_of_nonneg G β J hβ
        (boundaryGhostCoupling_nonneg
          (FK.boxBoundary 3 n) hH (fun _ => by norm_num))
        m'
  have hleD :=
    edgeCopySourcePairDataWeight_le_summand
      G β J D hD_nonneg
  have hle :
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m') ≤
        edgeCopySourcePairSummand G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
          (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m' := by
    simpa [D, edgeCopySourcePairDataWeight, G, J, m'] using hleD
  have hcoef_nonneg : 0 ≤ (β * H) * (β * H) :=
    mul_self_nonneg (β * H)
  exact mul_le_mul_of_nonneg_left hle hcoef_nonneg


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sourcePairSummand
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (hv : FK.boxBoundary 3 n d.1) :
    let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    let m' :=
      Function.update d.2.toSourceData.1
        (finiteBoundaryGhostBoundaryEdge n d.1)
        (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1)
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      (β * H) * (β * H) *
        edgeCopySourcePairSummand G β J
          (finiteBoundaryGhostOnePointSource 3 n)
          (∅ : Finset (Option (FK.boxVerts 3 n))) m' := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let m' :=
    Function.update d.2.toSourceData.1
      (finiteBoundaryGhostBoundaryEdge n d.1)
      (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1)
  by_cases hne :
      (finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).Nonempty
  · rcases hne with ⟨i, hi⟩
    have hiedge : i.1 = finiteBoundaryGhostBoundaryEdge n d.1 := by
      have hitarget :
          i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d :=
        (Finset.mem_filter.mp hi).1
      exact (Finset.mem_filter.mp hitarget).2
    have hleft :
        (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
          (β * H) * (β * H) *
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m') := by
      simpa [G, J, m'] using
        finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sq_decrement_weight
          hβ hH d hv
    have hright :
        (β * H) * (β * H) *
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m') ≤
          (β * H) * (β * H) *
            edgeCopySourcePairSummand G β J
              (finiteBoundaryGhostOnePointSource 3 n)
              (∅ : Finset (Option (FK.boxVerts 3 n))) m' := by
      simpa [G, J, m', hiedge] using
        finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_sq_decrement_weight_le_sourcePairSummand
          hβ hH d hi
    exact hleft.trans hright
  · have hempty :
        finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hne ⟨i, hi⟩
    have hsummand_nonneg :
        0 ≤ edgeCopySourcePairSummand G β J
          (finiteBoundaryGhostOnePointSource 3 n)
          (∅ : Finset (Option (FK.boxVerts 3 n))) m' := by
      exact
        edgeCopySourcePairSummand_nonneg G β J
          (finiteBoundaryGhostOnePointSource 3 n)
          (∅ : Finset (Option (FK.boxVerts 3 n))) m'
          hβ
          (boundaryGhostCoupling_nonneg
            (FK.boxBoundary 3 n) hH (fun _ => by norm_num))
    have hcoef_nonneg : 0 ≤ (β * H) * (β * H) :=
      mul_self_nonneg (β * H)
    have hrhs_nonneg :
        0 ≤
          (β * H) * (β * H) *
            edgeCopySourcePairSummand G β J
              (finiteBoundaryGhostOnePointSource 3 n)
              (∅ : Finset (Option (FK.boxVerts 3 n))) m' :=
      mul_nonneg hcoef_nonneg hsummand_nonneg
    simpa [G, J, m', hempty] using hrhs_nonneg


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sourcePairSummand
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (hv : FK.boxBoundary 3 n d.1) :
    let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    let m' :=
      Function.update d.2.toSourceData.1
        (finiteBoundaryGhostBoundaryEdge n d.1)
        (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1)
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      (β * H) * (β * H) *
        edgeCopySourcePairSummand G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
          (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m' := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let m' :=
    Function.update d.2.toSourceData.1
      (finiteBoundaryGhostBoundaryEdge n d.1)
      (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1)
  by_cases hne :
      (finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).Nonempty
  · rcases hne with ⟨i, hi⟩
    have hiedge : i.1 = finiteBoundaryGhostBoundaryEdge n d.1 := by
      have hitarget :
          i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d :=
        (Finset.mem_filter.mp hi).1
      exact (Finset.mem_filter.mp hitarget).2
    have hleft :
        (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
          (β * H) * (β * H) *
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m') := by
      simpa [G, J, m'] using
        finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sq_decrement_weight
          hβ hH d hv
    have hright :
        (β * H) * (β * H) *
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m') ≤
          (β * H) * (β * H) *
            edgeCopySourcePairSummand G β J
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
              (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m' := by
      simpa [G, J, m', hiedge] using
        finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_sq_decrement_weight_le_sourcePairSummand
          hβ hH d hi
    exact hleft.trans hright
  · have hempty :
        finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hne ⟨i, hi⟩
    have hsummand_nonneg :
        0 ≤ edgeCopySourcePairSummand G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
          (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m' := by
      exact
        edgeCopySourcePairSummand_nonneg G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
          (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m'
          hβ
          (boundaryGhostCoupling_nonneg
            (FK.boxBoundary 3 n) hH (fun _ => by norm_num))
    have hcoef_nonneg : 0 ≤ (β * H) * (β * H) :=
      mul_self_nonneg (β * H)
    have hrhs_nonneg :
        0 ≤
          (β * H) * (β * H) *
            edgeCopySourcePairSummand G β J
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
              (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m' :=
      mul_nonneg hcoef_nonneg hsummand_nonneg
    simpa [G, J, m', hempty] using hrhs_nonneg


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card_eq_source_add_complement
    {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d).card =
      (finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card +
      (finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card := by
  classical
  simpa [finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies,
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies] using
    (Finset.card_filter_add_card_filter_not
      (s := finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d)
      (p := fun i => i ∈ d.2.toSourceData.2.1)).symm


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_decrementedBoundaryMultiplicity_weight
    {β H : ℝ} {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
      (((d.2.toSourceData.1
          (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card]


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_source_add_complement
    {β H : ℝ} {n : ℕ}
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) +
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  simpa [finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies,
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies] using
    (Finset.sum_filter_add_sum_filter_not
      (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d)
      (fun i => i ∈ d.2.toSourceData.2.1)
      (fun _ =>
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)).symm


theorem
    finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_le_sourcePairSum_add
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostCollapsedTwoPointSourceData n v))
    (hv : FK.boxBoundary 3 n d.1) :
    let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
      (β * H) * (β * H) *
        edgeCopySourcePairSum G β J
          (finiteBoundaryGhostOnePointSource 3 n)
          (∅ : Finset (Option (FK.boxVerts 3 n))) +
      (β * H) * (β * H) *
        edgeCopySourcePairSum G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
          (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let m' :=
    Function.update d.2.toSourceData.1
      (finiteBoundaryGhostBoundaryEdge n d.1)
      (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1)
  let A₀ := finiteBoundaryGhostOnePointSource 3 n
  let B₀ := (∅ : Finset (Option (FK.boxVerts 3 n)))
  let A₁ :=
    (({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
  let B₁ :=
    (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
  have hJ_nonneg : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg
      (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  have hcoef_nonneg : 0 ≤ (β * H) * (β * H) :=
    mul_self_nonneg (β * H)
  have hsource_summand :
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
        (β * H) * (β * H) *
          edgeCopySourcePairSummand G β J A₀ B₀ m' := by
    simpa [G, J, m', A₀, B₀] using
      finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sourcePairSummand
        hβ hH d hv
  have hsource_to_sum :
      (β * H) * (β * H) *
          edgeCopySourcePairSummand G β J A₀ B₀ m' ≤
        (β * H) * (β * H) *
          edgeCopySourcePairSum G β J A₀ B₀ := by
    exact
      mul_le_mul_of_nonneg_left
        (edgeCopySourcePairSummand_le_edgeCopySourcePairSum
          G β J A₀ B₀ m' hβ hJ_nonneg)
        hcoef_nonneg
  have hsource :
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
        (β * H) * (β * H) *
          edgeCopySourcePairSum G β J A₀ B₀ :=
    hsource_summand.trans hsource_to_sum
  have hcomp_summand :
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
        (β * H) * (β * H) *
          edgeCopySourcePairSummand G β J A₁ B₁ m' := by
    simpa [G, J, m', A₁, B₁] using
      finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sourcePairSummand
        hβ hH d hv
  have hcomp_to_sum :
      (β * H) * (β * H) *
          edgeCopySourcePairSummand G β J A₁ B₁ m' ≤
        (β * H) * (β * H) *
          edgeCopySourcePairSum G β J A₁ B₁ := by
    exact
      mul_le_mul_of_nonneg_left
        (edgeCopySourcePairSummand_le_edgeCopySourcePairSum
          G β J A₁ B₁ m' hβ hJ_nonneg)
        hcoef_nonneg
  have hcomp :
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤
        (β * H) * (β * H) *
          edgeCopySourcePairSum G β J A₁ B₁ :=
    hcomp_summand.trans hcomp_to_sum
  calc
    (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) =
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) +
      (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
        finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
        finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_source_add_complement
          (β := β) (H := H) d
    _ ≤
      (β * H) * (β * H) * edgeCopySourcePairSum G β J A₀ B₀ +
      (β * H) * (β * H) * edgeCopySourcePairSum G β J A₁ B₁ :=
        add_le_add hsource hcomp


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundaryCopy_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) =
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro d _hd
  exact
    (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_decrementedBoundaryMultiplicity_weight
      (β := β) (H := H) d).symm


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sourcePairSum_add
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    let G := Sharpness.withGhost (FK.boxGraph 3 n)
    let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) ≤
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (β * H) * (β * H) *
            edgeCopySourcePairSum G β J
              (finiteBoundaryGhostOnePointSource 3 n)
              (∅ : Finset (Option (FK.boxVerts 3 n))) +
          (β * H) * (β * H) *
            edgeCopySourcePairSum G β J
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
              (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})) := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  calc
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) =
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundaryCopy_sum
          (β := β) (H := H) Ω
    _ ≤
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (β * H) * (β * H) *
            edgeCopySourcePairSum G β J
              (finiteBoundaryGhostOnePointSource 3 n)
              (∅ : Finset (Option (FK.boxVerts 3 n))) +
          (β * H) * (β * H) *
            edgeCopySourcePairSum G β J
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1})
              (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        have hv : FK.boxBoundary 3 n d.1 :=
          finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary Ω hd
        simpa [G, J] using
          finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_le_sourcePairSum_add
            hβ hH d hv


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_sourcePairSum_add_image_sum_eq_regrouped
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
    Finset.sum I.image (fun d => onePoint + boundaryPair d.1) =
      (((I.image.card : ℕ) : ℝ) * onePoint) +
        ∑ v ∈ Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v := by
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
  have hboundary :
      Finset.sum I.image (fun d => boundaryPair d.1) =
        ∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v := by
    calc
      Finset.sum I.image (fun d => boundaryPair d.1) =
          ∑ v ∈ B,
            ∑ d ∈ I.image.filter (fun d => d.1 = v),
              boundaryPair d.1 := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := I.image) (t := B) (g := fun d => d.1)
          hmaps (fun d => boundaryPair d.1)]
      _ =
          ∑ v ∈ B,
            (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
              boundaryPair v := by
        refine Finset.sum_congr rfl ?_
        intro v _hv
        have hinner :
            (∑ d ∈ I.image.filter (fun d => d.1 = v), boundaryPair d.1) =
              ∑ _d ∈ I.image.filter (fun d => d.1 = v), boundaryPair v := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          exact congrArg boundaryPair (Finset.mem_filter.mp hd).2
        rw [hinner, Finset.sum_const, nsmul_eq_mul]
  change
    Finset.sum I.image (fun d => onePoint + boundaryPair d.1) =
      (((I.image.card : ℕ) : ℝ) * onePoint) +
        ∑ v ∈ B,
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v
  calc
    Finset.sum I.image (fun d => onePoint + boundaryPair d.1) =
        Finset.sum I.image (fun _ => onePoint) +
          Finset.sum I.image (fun d => boundaryPair d.1) := by
      rw [Finset.sum_add_distrib]
    _ =
        (((I.image.card : ℕ) : ℝ) * onePoint) +
          Finset.sum I.image (fun d => boundaryPair d.1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ =
        (((I.image.card : ℕ) : ℝ) * onePoint) +
          ∑ v ∈ B,
            (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
              boundaryPair v := by
      rw [hboundary]


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_regrouped_sourcePairSum
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
    Finset.sum I.image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) ≤
      (((I.image.card : ℕ) : ℝ) * onePoint) +
        ∑ v ∈ Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v := by
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
  calc
    Finset.sum I.image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) ≤
      Finset.sum I.image (fun d => onePoint + boundaryPair d.1) := by
        simpa [I, G, J, C, onePoint, boundaryPair] using
          finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sourcePairSum_add
            hβ hH Ω
    _ =
      (((I.image.card : ℕ) : ℝ) * onePoint) +
        ∑ v ∈ Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v),
          (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) *
            boundaryPair v := by
        simpa [I, G, J, C, onePoint, boundaryPair] using
          finiteBoundaryGhostCollapsedCutoffDecrementIndex_sourcePairSum_add_image_sum_eq_regrouped
            (β := β) (H := H) Ω


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundarySource_add_complement_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) =
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) +
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  calc
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) =
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) :=
        finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundaryCopy_sum
          (β := β) (H := H) Ω
    _ =
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) +
          (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        exact
          finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_source_add_complement
            (β := β) (H := H) d
    _ =
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) +
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d,
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
        rw [Finset.sum_add_distrib]


theorem
    finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sq_decrement_weight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (((d.2.toSourceData.1
              (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) *
            finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) ≤
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image
        (fun d =>
          (β * H) * (β * H) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                (Function.update d.2.toSourceData.1
                  (finiteBoundaryGhostBoundaryEdge n d.1)
                  (d.2.toSourceData.1
                    (finiteBoundaryGhostBoundaryEdge n d.1) - 1)))) := by
  classical
  refine Finset.sum_le_sum ?_
  intro d hd
  exact
      finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_sq_decrement_weight
        hβ hH d
      (finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary Ω hd)


end Exact3D
end StatMech
