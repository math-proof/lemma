/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part5
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem reciprocalKWDet_list_eq_bounded_resum
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (q : Complex) (hq : q ≠ 0)
    (edges : List (Sym2 V)) (hedges : edges.Nodup) :
    q ^ (2 * edges.length) *
        (1 - kwGraphTransition G
          (ons_setGraphEdgeWeightList weight q⁻¹ edges)
          embedding.turnPhase).det =
      ons_boundedReciprocalKWDetResum G embedding weight q edges := by
  induction edges generalizing weight with
  | nil => simp [ons_setGraphEdgeWeightList,
      ons_boundedReciprocalKWDetResum]
  | cons edge edges ih =>
      rw [List.nodup_cons] at hedges
      have hcomm :
          ons_setGraphEdgeWeightList weight q⁻¹ (edge :: edges) =
            ons_setGraphEdgeWeight
              (ons_setGraphEdgeWeightList weight q⁻¹ edges)
              edge q⁻¹ := rfl
      rw [hcomm, List.length_cons, Nat.mul_succ]
      rw [pow_add, pow_two]
      have hlocal := reciprocalKWDet_eq_bounded_three_point G embedding
        (ons_setGraphEdgeWeightList weight q⁻¹ edges) edge q hq
      rw [show q ^ (2 * edges.length) * (q * q) *
          (1 - kwGraphTransition G
            (ons_setGraphEdgeWeight
              (ons_setGraphEdgeWeightList weight q⁻¹ edges)
              edge q⁻¹) embedding.turnPhase).det =
          q ^ (2 * edges.length) *
            (q ^ 2 *
              (1 - kwGraphTransition G
                (ons_setGraphEdgeWeight
                  (ons_setGraphEdgeWeightList weight q⁻¹ edges)
                  edge q⁻¹) embedding.turnPhase).det) by ring]
      rw [hlocal, Finset.mul_sum]
      unfold ons_boundedReciprocalKWDetResum
      apply Finset.sum_congr rfl
      intro s hs
      have hind := ih
        (ons_setGraphEdgeWeight weight edge
          (ons_reciprocalInterpolationValue q s)) hedges.2
      rw [ons_setGraphEdgeWeightList_set_comm
        weight edge (ons_reciprocalInterpolationValue q s) q⁻¹
        edges hedges.1] at hind
      calc
        q ^ (2 * edges.length) *
            (ons_reciprocalInterpolationCoeff q s *
              (1 - kwGraphTransition G
                (ons_setGraphEdgeWeight
                  (ons_setGraphEdgeWeightList weight q⁻¹ edges) edge
                  (ons_reciprocalInterpolationValue q s))
                embedding.turnPhase).det) =
          ons_reciprocalInterpolationCoeff q s *
            (q ^ (2 * edges.length) *
              (1 - kwGraphTransition G
                (ons_setGraphEdgeWeight
                  (ons_setGraphEdgeWeightList weight q⁻¹ edges) edge
                  (ons_reciprocalInterpolationValue q s))
                embedding.turnPhase).det) := by ring
        _ = _ := by rw [hind]


end
end StatMech.Onsager
