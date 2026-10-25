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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part62
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha_map
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (a : (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).α) :
    (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map
        (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha
          Ω hv a) =
      ⟨v, (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).map a⟩ := by
  rfl

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_onePointSourceCutoff_eq_collapsedVertexCutoffDecrementIndex_domain_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (finiteBoundaryGhostOnePointSourceCutoff Ω) v =
      Finset.sum
        (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).domain
        (fun a =>
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
            ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).map
              a)) := by
  classical
  let Ωsrc := finiteBoundaryGhostOnePointSourceCutoff Ω
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ωsrc v =
        ∑ m ∈ Ωsrc.attach,
          Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m.1 v)
            (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
              β H m.1 v) := by
      simpa [Ωsrc] using
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_attach_sum
          β H n Ωsrc v
    _ =
        Finset.sum I.domain
          (fun a =>
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
              (I.map a)) := by
      unfold I finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl ?_
      intro m _hm
      calc
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m.1 v)
            (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
              β H m.1 v) =
          ∑ p : finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m.1 v,
            finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand
              β H n m.1 v p := by
            exact
              (finiteBoundaryGhostDecrementedSourceWeightVertexFiber_univ_sum_eq_pair_sum
                β H m.1 v).symm
        _ =
          ∑ p : finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m.1 v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
              (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData
                m.1 v
                (by
                  exact
                    ((finiteBoundaryGhostOnePointSourceCutoff_mem Ω m.1).mp
                      m.2).2)
                p.2) := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            unfold finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand
            simpa [finiteBoundaryGhostCollapsedTwoPointSourceDataWeight] using
              (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight
                (β := β) (H := H) m.1 (v := v) p.2)

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_domain_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v =
      Finset.sum
        (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).domain
        (fun a =>
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
            ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).map
              a)) := by
  rw [← finiteBoundaryGhostOnePointSourceCutoff_eq_filter_fullSourceOnePoint Ω]
  exact
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_onePointSourceCutoff_eq_collapsedVertexCutoffDecrementIndex_domain_sum
      (β := β) (H := H) Ω v

set_option linter.style.longLine false in


theorem finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_domain_sum_eq_image_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    Finset.sum
        (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).domain
        (fun a =>
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
            ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).map
              a)) =
      ∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image,
        (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber
            d).card : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d :=
  FinsetFiberIndex.sum_fiber_weight
    (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v)
    (finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H)

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_image_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v =
      ∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image,
        (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber
            d).card : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
  rw [
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_domain_sum,
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_domain_sum_eq_image_sum]


end Exact3D
end StatMech
