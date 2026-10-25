/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Def.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem boundaryPartitionJ_high_temp
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V) :
    boundaryPartitionJ G beta J interior =
      (2 : ℝ) ^ interior.card *
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ∑ H ∈ G.edgeFinset.powerset,
            if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
              highTempSubgraphWeight beta J H else 0 := by
  unfold boundaryPartitionJ
  simp_rw [boltzmannJ_high_temp_factor G beta J]
  have hexpand (s : ConfigSpace ↑interior) :
      (∏ e ∈ G.edgeFinset,
          (1 + Real.tanh (beta * J e) *
            bond (extendInteriorPlus interior s) e)) =
        ∑ H ∈ G.edgeFinset.powerset,
          ∏ e ∈ H, (Real.tanh (beta * J e) *
            bond (extendInteriorPlus interior s) e) :=
    Finset.prod_one_add _
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [show (2 : ℝ) ^ interior.card *
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        (∑ H ∈ G.edgeFinset.powerset,
          if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
            highTempSubgraphWeight beta J H else 0) =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        ((2 : ℝ) ^ interior.card *
          ∑ H ∈ G.edgeFinset.powerset,
            if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
              highTempSubgraphWeight beta J H else 0) by ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  have hHsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hH
  have hfactor (s : ConfigSpace ↑interior) :
      (∏ e ∈ H, (Real.tanh (beta * J e) *
        bond (extendInteriorPlus interior s) e)) =
      highTempSubgraphWeight beta J H *
        ∏ e ∈ H, bond (extendInteriorPlus interior s) e := by
    unfold highTempSubgraphWeight
    rw [Finset.prod_mul_distrib]
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  have hbonds (s : ConfigSpace ↑interior) :
      (∏ e ∈ H, bond (extendInteriorPlus interior s) e) =
        ∏ e ∈ G.edgeFinset,
          bond (extendInteriorPlus interior s) e ^ edgeIndicatorCurrent H e := by
    rw [show (∏ e ∈ H, bond (extendInteriorPlus interior s) e) =
        ∏ e ∈ H,
          bond (extendInteriorPlus interior s) e ^ edgeIndicatorCurrent H e by
      apply Finset.prod_congr rfl
      intro e he
      simp [edgeIndicatorCurrent, he]]
    apply Finset.prod_subset hHsub
    intro e heG heH
    simp [edgeIndicatorCurrent, heH]
  simp_rw [hbonds]
  rw [interiorSpinSum_monomial_eq G interior (edgeIndicatorCurrent H)]
  by_cases hs : sources G (edgeIndicatorCurrent H) ∩ interior = ∅ <;>
    simp [hs, mul_assoc, mul_comm, mul_left_comm]

theorem boundaryPartitionJ_unit_high_temp
    (beta : ℝ) (interior : Finset V) :
    boundaryPartitionJ G beta (fun _ => 1) interior =
      (2 : ℝ) ^ interior.card *
        Real.cosh beta ^ G.edgeFinset.card *
          boundaryParityPartition G beta interior := by
  rw [boundaryPartitionJ_high_temp]
  simp only [mul_one, Finset.prod_const]
  change ((2 : ℝ) ^ interior.card * Real.cosh beta ^ G.edgeFinset.card) *
      (∑ H ∈ G.edgeFinset.powerset,
        if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
          highTempSubgraphWeight beta (fun _ => 1) H else 0) =
    ((2 : ℝ) ^ interior.card * Real.cosh beta ^ G.edgeFinset.card) *
      boundaryParityPartition G beta interior
  congr 1
  unfold boundaryParityPartition boundaryParityAllowed
  apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
  · intro H hgap
    have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.mp hgap).2
    have hsub : ¬ H ⊆ G.edgeFinset := by simpa using hnot
    simp [hsub]
  · intro H hpow
    have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hpow
    by_cases hs : sources G (edgeIndicatorCurrent H) ∩ interior = ∅ <;>
      simp [highTempSubgraphWeight, hsub, hs]

theorem boundaryPartitionJ_deleted_high_temp
    (beta : ℝ) (interior : Finset V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    boundaryPartitionJ G beta (deletedEdgeCoupling F) interior =
      (2 : ℝ) ^ interior.card *
        Real.cosh beta ^ (G.edgeFinset.card - F.card) *
          boundaryParityAvoidSum G beta interior F := by
  rw [boundaryPartitionJ_high_temp,
    deletedEdgeCoupling_cosh_prod G beta F hF]
  change ((2 : ℝ) ^ interior.card *
      Real.cosh beta ^ (G.edgeFinset.card - F.card)) *
      (∑ H ∈ G.edgeFinset.powerset,
        if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
          highTempSubgraphWeight beta (deletedEdgeCoupling F) H else 0) =
    ((2 : ℝ) ^ interior.card *
      Real.cosh beta ^ (G.edgeFinset.card - F.card)) *
      boundaryParityAvoidSum G beta interior F
  congr 1
  unfold boundaryParityAvoidSum boundaryParityAllowed
  apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
  · intro H hgap
    have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.mp hgap).2
    have hsub : ¬ H ⊆ G.edgeFinset := by simpa using hnot
    simp [hsub]
  · intro H hpow
    have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hpow
    by_cases hs : sources G (edgeIndicatorCurrent H) ∩ interior = ∅
    · by_cases hd : Disjoint H F
      · have hw : highTempSubgraphWeight beta (deletedEdgeCoupling F) H =
            Real.tanh beta ^ H.card := by
          unfold highTempSubgraphWeight
          rw [← Finset.prod_const]
          apply Finset.prod_congr rfl
          intro e he
          have heF : e ∉ F := fun hef => Finset.disjoint_left.mp hd he hef
          simp [deletedEdgeCoupling, heF]
        simp [hsub, hs, hd, hw]
      · have hw : highTempSubgraphWeight beta (deletedEdgeCoupling F) H = 0 := by
          unfold highTempSubgraphWeight
          rw [Finset.not_disjoint_iff_nonempty_inter] at hd
          obtain ⟨e, he⟩ := hd
          apply Finset.prod_eq_zero (Finset.mem_inter.mp he).1
          simp [deletedEdgeCoupling, (Finset.mem_inter.mp he).2]
        simp [hsub, hs, hd, hw]
    · simp [hsub, hs]

theorem tsum_boundaryCurrentRawMass_fixedParity
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V)
    (H : Finset (Sym2 V)) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0) =
      boundaryParityRawMass G beta interior H *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  by_cases hH : H ⊆ G.edgeFinset
  · by_cases hsrc : sources G (edgeIndicatorCurrent H) ∩ interior = ∅
    · let f : EdgeCurrent G → ℝ := fun m =>
        if currentParitySupport G m = H then
          weight G beta (fun _ => 1) (ofEdgeFun G m) else 0
      have hf_nonneg : ∀ m, 0 ≤ f m := by
        intro m
        simp only [f]
        split
        · exact acw_weight_nonneg G beta (fun _ => 1)
            hbeta (fun _ => zero_le_one) _
        · exact le_rfl
      have hf_summable : Summable f := by
        refine Summable.of_nonneg_of_le hf_nonneg (fun m => ?_)
          (summable_norm_weight_ofEdgeFun G beta (fun _ => 1)).of_norm
        simp only [f]
        split
        · exact le_rfl
        · exact acw_weight_nonneg G beta (fun _ => 1)
            hbeta (fun _ => zero_le_one) _
      calc
        (∑' m : EdgeCurrent G,
            if currentParitySupport G m = H then
              boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0) =
            ∑' m : EdgeCurrent G, ENNReal.ofReal (f m) := by
          apply tsum_congr
          intro m
          by_cases hm : currentParitySupport G m = H
          · have hsource :
                sources G (ofEdgeFun G m) ∩ interior = ∅ := by
              rw [sources_eq_sources_currentParitySupport G m, hm]
              exact hsrc
            simp [boundaryCurrentRawMass, f, hm, hsource]
          · simp [f, hm]
        _ = ENNReal.ofReal (∑' m : EdgeCurrent G, f m) :=
          (ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf_summable).symm
        _ = ENNReal.ofReal
              (Real.cosh beta ^ G.edgeFinset.card *
                Real.tanh beta ^ H.card) := by
          apply congrArg ENNReal.ofReal
          exact fixedParity_weight_tsum_closed G beta hbeta H hH
        _ = boundaryParityRawMass G beta interior H *
              ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          simp [boundaryParityRawMass, boundaryParityAllowed, hH, hsrc,
            mul_comm]
    · have hzero : ∀ m : EdgeCurrent G,
          (if currentParitySupport G m = H then
            boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0) = 0 := by
        intro m
        by_cases hm : currentParitySupport G m = H
        · have hsource : sources G (ofEdgeFun G m) ∩ interior ≠ ∅ := by
            rw [sources_eq_sources_currentParitySupport G m, hm]
            exact hsrc
          simp [boundaryCurrentRawMass, hm, hsource]
        · simp [hm]
      simp_rw [hzero]
      simp [boundaryParityRawMass, boundaryParityAllowed, hH, hsrc]
  · have hne : ∀ m : EdgeCurrent G, currentParitySupport G m ≠ H := by
      intro m hm
      apply hH
      rw [← hm]
      exact currentParitySupport_subset G m
    simp_rw [if_neg (hne _)]
    simp [boundaryParityRawMass, boundaryParityAllowed, hH]

theorem boundaryCurrentSum_eq_boundaryParityPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V) :
    ENNReal.ofReal (boundaryCurrentSum G beta (fun _ => 1) interior) =
      ENNReal.ofReal (boundaryParityPartition G beta interior) *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  rw [← tsum_boundaryCurrentRawMass G beta (fun _ => 1) hbeta
    (fun _ => zero_le_one) interior]
  let p : EdgeCurrent G → Finset (Sym2 V) := currentParitySupport G
  have hfiber := ENNReal.tsum_fiberwise
    (boundaryCurrentRawMass G beta (fun _ => 1) interior) p
  rw [tsum_fintype] at hfiber
  rw [← hfiber]
  simp_rw [show ∀ H : Finset (Sym2 V),
      (∑' b : ↑(p ⁻¹' {H}),
        boundaryCurrentRawMass G beta (fun _ => 1) interior b.1) =
      ∑' m : EdgeCurrent G,
        if currentParitySupport G m = H then
          boundaryCurrentRawMass G beta (fun _ => 1) interior m else 0 by
    intro H
    rw [tsum_subtype]
    apply tsum_congr
    intro m
    by_cases hm : currentParitySupport G m = H
    · simp [p, hm]
    · simp [p, hm]]
  simp_rw [tsum_boundaryCurrentRawMass_fixedParity G beta hbeta interior]
  rw [← Finset.sum_mul]
  unfold boundaryParityRawMass boundaryParityPartition
  rw [← ENNReal.ofReal_sum_of_nonneg]
  intro H hH
  split
  · exact pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
  · exact le_rfl

end StatMech.FrontierB
