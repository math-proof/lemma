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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part59
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_mem
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n)) :
    a ∈ finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport n Ω ↔
      a.1 ∈ Ω := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport
  constructor
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨b, hb, hbmap⟩
    have hbΩ : b.1.1 ∈ Ω := b.1.2
    have hfst : b.1.1 = a.1 := by
      simpa [finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupportEmbedding]
        using congrArg Sigma.fst hbmap
    simpa [← hfst] using hbΩ
  · intro ha
    refine Finset.mem_map.mpr ?_
    refine ⟨⟨⟨a.1, ha⟩, a.2⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_attach _ ⟨a.1, ha⟩, Finset.mem_univ _⟩


theorem
    finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_sum_eq_cutoffSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport n Ω,
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) =
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω := by
  classical
  unfold finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport
  rw [Finset.sum_map, Finset.sum_sigma]
  calc
    (∑ m ∈ Ω.attach,
        ∑ a ∈ (Finset.univ :
          Finset (finiteBoundaryGhostDecrementedSourceWeightFiber n m.1)),
          finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n
            ((finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupportEmbedding
              n Ω) ⟨m, a⟩))
        =
      ∑ m ∈ Ω.attach,
        finiteBoundaryGhostDecrementedSourceWeightSummand β H n m.1 := by
      refine Finset.sum_congr rfl ?_
      intro m _hm
      change
        (∑ a : finiteBoundaryGhostDecrementedSourceWeightFiber n m.1,
          finiteBoundaryGhostDecrementedSourceWeightFiberSummand β H n m.1 a) =
          finiteBoundaryGhostDecrementedSourceWeightSummand β H n m.1
      rw [finiteBoundaryGhostDecrementedSourceWeightSummand_eq_tsum_fiber
        β H n m.1, tsum_fintype]
    _ =
      ∑ m ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightSummand β H n m := by
      rw [Finset.sum_attach]
    _ = finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω :=
      (finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand
        β H n Ω).symm


theorem finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_currentSupport_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset (Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n))) :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) ≤
      ∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport
          n (Ω.image Sigma.fst),
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
  · intro a ha
    rw [finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_mem]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · intro a _ha _hnot
    exact finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_nonneg
      (β := β) (H := H) hβ hH a


theorem finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_cutoffSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset (Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n))) :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) ≤
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum
        β H n (Ω.image Sigma.fst) := by
  calc
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) ≤
      ∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport
          n (Ω.image Sigma.fst),
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a :=
      finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_currentSupport_sum
        (β := β) (H := H) hβ hH Ω
    _ =
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum
        β H n (Ω.image Sigma.fst) :=
      finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_sum_eq_cutoffSum
        β H n (Ω.image Sigma.fst)


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_selectedPairCutoffSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      finiteBoundaryGhostSelectedPairCutoffSum β H n Ω := by
  classical
  unfold finiteBoundaryGhostSelectedPairCutoffSum
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m)
      ≤
        ∑ m ∈ Ω,
          ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            ((if Sharpness.RandomCurrent.sources
                  (Sharpness.FluxEdgeCopy.endsM
                    (Sharpness.withGhost (FK.boxGraph 3 n)) m)
                  (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                    (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
                finiteBoundaryGhostOnePointSource 3 n then
                (1 : ℝ)
              else
                0) *
              (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
              Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                  m) := by
      refine Finset.sum_le_sum ?_
      intro m _hm
      unfold finiteBoundaryGhostCollapsedSourceSummand
      exact
        finiteBoundaryGhostCollapsedSummand_le_crossingPairCountSummand_sum
          (β := β) (H := H) hβ hH m
    _ =
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ∑ m ∈ Ω,
            ((if Sharpness.RandomCurrent.sources
                  (Sharpness.FluxEdgeCopy.endsM
                    (Sharpness.withGhost (FK.boxGraph 3 n)) m)
                  (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                    (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
                finiteBoundaryGhostOnePointSource 3 n then
                (1 : ℝ)
              else
                0) *
              (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
              Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                  m) := by
      rw [Finset.sum_comm]
    _ =
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ∑ m ∈ Ω,
            ∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
              (if Sharpness.RandomCurrent.sources
                    (Sharpness.FluxEdgeCopy.endsM
                      (Sharpness.withGhost (FK.boxGraph 3 n)) m)
                    (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                      (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
                  finiteBoundaryGhostOnePointSource 3 n then
                  (1 : ℝ)
                else
                  0) *
                Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
                  (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                  (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                    m) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      refine Finset.sum_congr rfl ?_
      intro m _hm
      rw [finiteBoundaryGhostBoundaryCrossingPairCountSummand_eq_sum_pairs]


theorem finiteBoundaryGhostSelectedPairCutoffSum_le_decrementedSourceWeightCutoffSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostSelectedPairCutoffSum β H n Ω ≤
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω := by
  classical
  unfold finiteBoundaryGhostSelectedPairCutoffSum
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum
  refine Finset.sum_le_sum ?_
  intro v hv
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  refine Finset.sum_le_sum ?_
  intro m _hm
  exact
    finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourceWeightSum
      (β := β) (H := H) hβ hH m hvbdry


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_decrementedSourceWeightCutoffSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω :=
  (finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_selectedPairCutoffSum
    (β := β) (H := H) hβ hH Ω).trans
    (finiteBoundaryGhostSelectedPairCutoffSum_le_decrementedSourceWeightCutoffSum
      (β := β) (H := H) hβ hH Ω)


end Exact3D
end StatMech
