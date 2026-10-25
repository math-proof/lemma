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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part47
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostCollapsedSourceSummand_nonneg
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    0 ≤ finiteBoundaryGhostCollapsedSourceSummand β H n m := by
  classical
  unfold finiteBoundaryGhostCollapsedSourceSummand
  have hind :
      0 ≤
        if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0 := by
    split <;> norm_num
  have hcard : 0 ≤ ((finiteBoundaryGhostSourceSector m).card : ℝ) := by
    exact_mod_cast Nat.zero_le (finiteBoundaryGhostSourceSector m).card
  have hw :
      0 ≤
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) := by
    refine
      weight_ofEdgeFun_nonneg_of_nonneg
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        hβ ?_ m
    exact boundaryGhostCoupling_nonneg
      (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  exact mul_nonneg (mul_nonneg hind hcard) hw


theorem finiteBoundaryGhostCollapsedSourceSummand_tsum_eq_emptyCollapsedSum
    (β H : ℝ) (n : ℕ) :
    (∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
      finiteBoundaryGhostCollapsedSourceSummand β H n m) =
      edgeCopySourcePairEmptyCollapsedSum
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource 3 n) := by
  rfl


theorem finiteBoundaryGhostCollapsedSourceSummand_summable
    (β H : ℝ) (n : ℕ) :
    Summable
      (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
        finiteBoundaryGhostCollapsedSourceSummand β H n m) := by
  simpa [finiteBoundaryGhostCollapsedSourceSummand,
    finiteBoundaryGhostSourceSector] using
    edgeCopySourcePairEmptyCollapsedSummand_summable
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (finiteBoundaryGhostOnePointSource 3 n)


theorem finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_emptyCollapsedSum
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      edgeCopySourcePairEmptyCollapsedSum
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource 3 n) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m)
        ≤
        ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
          finiteBoundaryGhostCollapsedSourceSummand β H n m :=
      (finiteBoundaryGhostCollapsedSourceSummand_summable β H n).sum_le_tsum
        Ω
        (fun m _hm =>
          finiteBoundaryGhostCollapsedSourceSummand_nonneg
            (β := β) (H := H) hβ hH m)
    _ =
      edgeCopySourcePairEmptyCollapsedSum
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource 3 n) :=
      finiteBoundaryGhostCollapsedSourceSummand_tsum_eq_emptyCollapsedSum β H n


theorem tsum_le_of_all_finset_sum_le
    {α : Type*} {f : α → ℝ} {C : ℝ}
    (hf : Summable f)
    (h : ∀ Ω : Finset α, (∑ a ∈ Ω, f a) ≤ C) :
    (∑' a, f a) ≤ C := by
  have ht :
      Filter.Tendsto (fun Ω : Finset α => ∑ a ∈ Ω, f a)
        (SummationFilter.unconditional α).filter (𝓝 (∑' a, f a)) :=
    hf.hasSum
  exact isClosed_Iic.mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun Ω => h Ω))


theorem
    finiteBoundaryGhostCollapsedSourceSummand_le_boundaryMultiplicityDenominatorSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    finiteBoundaryGhostCollapsedSourceSummand β H n m ≤
      finiteBoundaryGhostBoundaryMultiplicityDenominatorSum β H n m := by
  unfold finiteBoundaryGhostCollapsedSourceSummand
    finiteBoundaryGhostBoundaryMultiplicityDenominatorSum
  exact
    finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum_sum
      (β := β) (H := H) hβ hH m


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityDenominatorSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ m ∈ Ω,
        finiteBoundaryGhostBoundaryMultiplicityDenominatorSum β H n m := by
  refine Finset.sum_le_sum ?_
  intro m _hm
  exact
    finiteBoundaryGhostCollapsedSourceSummand_le_boundaryMultiplicityDenominatorSum
      (β := β) (H := H) hβ hH m


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_emptyCollapsedSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (∑ m ∈ Ω,
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ)) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m)
      ≤
        ∑ m ∈ Ω,
          finiteBoundaryGhostBoundaryMultiplicityDenominatorSum β H n m :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityDenominatorSum
        (β := β) (H := H) hβ hH Ω
    _ =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (∑ m ∈ Ω,
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ)) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
      unfold finiteBoundaryGhostBoundaryMultiplicityDenominatorSum
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro v _hv
      rw [Finset.sum_mul]


theorem finiteBoundaryGhostCollapsedTwoPointDenominator_eq_currentSum_mul
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) :
    edgeCopySourcePairEmptyCollapsedSum
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) =
      Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
      Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (∅ : Finset (Option (FK.boxVerts 3 n))) := by
  simpa using
    edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})


theorem finiteBoundaryGhostCollapsedTwoPointDenominator_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (n : ℕ) (v : FK.boxVerts 3 n) :
    0 ≤
      edgeCopySourcePairEmptyCollapsedSum
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  rw [finiteBoundaryGhostCollapsedTwoPointDenominator_eq_currentSum_mul]
  have hJ :
      ∀ e, 0 ≤
        boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH
      (fun _ => by norm_num)
  exact mul_nonneg
    (Sharpness.ssl_currentSum_nonneg
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      hβ hJ
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
    (Sharpness.ssl_currentSum_nonneg
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      hβ hJ (∅ : Finset (Option (FK.boxVerts 3 n))))


end Exact3D
end StatMech
