/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part4
import Def.StatisticalMechanics.Code.FrontierB.BoundarySourceParity
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem tsum_boundarySourceCurrentRawMass_fixedParity
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior internalSources : Finset V)
    (H : Finset (Sym2 V)) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
          interior internalSources m else 0) =
      boundarySourceParityRawMass G beta interior internalSources H *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  by_cases hH : H ⊆ G.edgeFinset
  · by_cases hsrc :
        sources G (edgeIndicatorCurrent H) ∩ interior = internalSources
    · let f : EdgeCurrent G → ℝ := fun m ↦
        if currentParitySupport G m = H then
          weight G beta (fun _ ↦ 1) (ofEdgeFun G m) else 0
      have hf_nonneg : ∀ m, 0 ≤ f m := by
        intro m
        simp only [f]
        split
        · exact acw_weight_nonneg G beta (fun _ ↦ 1)
            hbeta (fun _ ↦ zero_le_one) _
        · exact le_rfl
      have hf_summable : Summable f := by
        refine Summable.of_nonneg_of_le hf_nonneg (fun m ↦ ?_)
          (summable_norm_weight_ofEdgeFun G beta (fun _ ↦ 1)).of_norm
        simp only [f]
        split
        · exact le_rfl
        · exact acw_weight_nonneg G beta (fun _ ↦ 1)
            hbeta (fun _ ↦ zero_le_one) _
      calc
        (∑' m : EdgeCurrent G,
            if currentParitySupport G m = H then
              boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
                interior internalSources m else 0) =
            ∑' m : EdgeCurrent G, ENNReal.ofReal (f m) := by
          apply tsum_congr
          intro m
          by_cases hm : currentParitySupport G m = H
          · have hsource :
                sources G (ofEdgeFun G m) ∩ interior = internalSources := by
              rw [sources_eq_sources_currentParitySupport G m, hm]
              exact hsrc
            simp [boundarySourceCurrentRawMass, f, hm, hsource]
          · simp [f, hm]
        _ = ENNReal.ofReal (∑' m : EdgeCurrent G, f m) :=
          (ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf_summable).symm
        _ = ENNReal.ofReal
              (Real.cosh beta ^ G.edgeFinset.card *
                Real.tanh beta ^ H.card) := by
          apply congrArg ENNReal.ofReal
          exact fixedParity_weight_tsum_closed G beta hbeta H hH
        _ = boundarySourceParityRawMass G beta interior internalSources H *
              ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          simp [boundarySourceParityRawMass,
            boundarySourceParityAllowed, hH, hsrc, mul_comm]
    · have hzero : ∀ m : EdgeCurrent G,
          (if currentParitySupport G m = H then
            boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
              interior internalSources m else 0) = 0 := by
        intro m
        by_cases hm : currentParitySupport G m = H
        · have hsource :
              sources G (ofEdgeFun G m) ∩ interior ≠ internalSources := by
            rw [sources_eq_sources_currentParitySupport G m, hm]
            exact hsrc
          simp [boundarySourceCurrentRawMass, hm, hsource]
        · simp [hm]
      simp_rw [hzero]
      simp [boundarySourceParityRawMass,
        boundarySourceParityAllowed, hH, hsrc]
  · have hne : ∀ m : EdgeCurrent G, currentParitySupport G m ≠ H := by
      intro m hm
      apply hH
      rw [← hm]
      exact currentParitySupport_subset G m
    simp_rw [if_neg (hne _)]
    simp [boundarySourceParityRawMass,
      boundarySourceParityAllowed, hH]

theorem boundarySourceCurrentSum_eq_parityPartition
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior internalSources : Finset V) :
    ENNReal.ofReal
        (boundarySourceCurrentSum G beta (fun _ ↦ 1)
          interior internalSources) =
      ENNReal.ofReal
          (boundarySourceParityPartition G beta interior internalSources) *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  rw [← tsum_boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
    hbeta (fun _ ↦ zero_le_one) interior internalSources]
  let p : EdgeCurrent G → Finset (Sym2 V) := currentParitySupport G
  have hfiber := ENNReal.tsum_fiberwise
    (boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
      interior internalSources) p
  rw [tsum_fintype] at hfiber
  rw [← hfiber]
  simp_rw [show ∀ H : Finset (Sym2 V),
      (∑' b : ↑(p ⁻¹' {H}),
        boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
          interior internalSources b.1) =
      ∑' m : EdgeCurrent G,
        if currentParitySupport G m = H then
          boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
            interior internalSources m else 0 by
    intro H
    rw [tsum_subtype]
    apply tsum_congr
    intro m
    by_cases hm : currentParitySupport G m = H
    · simp [p, hm]
    · simp [p, hm]]
  simp_rw [tsum_boundarySourceCurrentRawMass_fixedParity
    G beta hbeta interior internalSources]
  rw [← Finset.sum_mul]
  unfold boundarySourceParityRawMass boundarySourceParityPartition
  rw [← ENNReal.ofReal_sum_of_nonneg]
  intro H hH
  split
  · exact pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
  · exact le_rfl

end StatMech.FrontierB
