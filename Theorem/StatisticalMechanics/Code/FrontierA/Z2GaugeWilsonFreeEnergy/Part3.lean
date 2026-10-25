/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonSupport
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem multibondDisorderFreeEnergy_abs_le
    (ends : P → V × V) (J : P → Real) (D : Finset P) :
    |multibondDisorderFreeEnergy ends J D| ≤
      2 * ∑ p ∈ D, |J p| := by
  unfold multibondDisorderFreeEnergy
  rw [multibondIsingPartition_eq_Z_neg_one,
    multibondIsingPartition_eq_Z_neg_one]
  simpa using StatMech.Ising.logZ_dist_le (-1)
    (multibondIsingAction ends J)
    (multibondIsingAction ends (multibondTwistCoupling J D))
    (2 * ∑ p ∈ D, |J p|)
    (multibondIsingAction_twist_sub_abs_le ends J D)


theorem multibondIsing_twist_partition_ratio_eq_disorderRatio
    (root : V) (ends : P → V × V) (J : P → Real) (D : Finset P) :
    multibondIsingPartition ends (multibondTwistCoupling J D) /
        multibondIsingPartition ends J =
      (∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1 ∆ D, Real.exp (-2 * J p)) /
        (∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1, Real.exp (-2 * J p)) := by
  rw [multibondIsingPartition_twist_eq_shiftedActivity]
  rw [multibondIsingPartition_eq_two_mul_anchored]
  rw [← Finset.mul_sum]
  have hbulk : 2 * Real.exp (∑ p : P, J p) ≠ 0 := by positivity
  field_simp


theorem cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) =
      multibondIsingPartition cubicalDualEnds
          (multibondTwistCoupling (fun p => gaugeDualCoupling (K p))
            (cubicalXYSheet k)) /
        multibondIsingPartition cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) := by
  rw [cubicalXYWilsonExpectation_eq_typedDisorderRatio ha hb hc k K hK]
  symm
  exact multibondIsing_twist_partition_ratio_eq_disorderRatio
    none cubicalDualEnds (fun p => gaugeDualCoupling (K p))
      (cubicalXYSheet k)


theorem neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p) :
    -Real.log
        (gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k)) =
      multibondDisorderFreeEnergy cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) (cubicalXYSheet k) := by
  rw [cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio ha hb hc k K hK]
  unfold multibondDisorderFreeEnergy
  rw [Real.log_div
    (multibondIsingPartition_pos _ _).ne'
    (multibondIsingPartition_pos _ _).ne']
  ring


@[simp] theorem card_cubicalXYSheet
    {a b c : Nat} (k : Fin (c + 1)) :
    (cubicalXYSheet (a := a) (b := b) k).card = a * b := by
  unfold cubicalXYSheet
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    rcases x with ⟨i, j⟩
    rcases y with ⟨i', j'⟩
    simp only at hxy
    cases hxy
    rfl


theorem cubicalXYWilsonFreeEnergy_mem_Icc
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p) :
    -Real.log
        (gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k)) ∈
      Set.Icc 0
        (2 * ∑ p ∈ cubicalXYSheet k, |gaugeDualCoupling (K p)|) := by
  have hpos : 0 <
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) :=
    (gaugeWilsonExpectation_pos_iff_exists_boundary
      cubicalPlaquetteIncidence K hK (cubicalXYLoop k)).mpr
      ⟨cubicalXYSheet k, cubicalXYSheet_hasWilsonBoundary k⟩
  have hle :
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) ≤ 1 :=
    (gaugeWilsonExpectation_mem_Icc
      cubicalPlaquetteIncidence K hK (cubicalXYLoop k)).2
  constructor
  · rw [neg_nonneg]
    exact Real.log_nonpos hpos.le hle
  · rw [neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
      ha hb hc k K hK]
    exact le_trans (le_abs_self _)
      (multibondDisorderFreeEnergy_abs_le cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) (cubicalXYSheet k))


theorem cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (beta : Real) (hbeta : 0 < beta) :
    -Real.log
        (gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette a b c => beta) (cubicalXYLoop k)) ≤
      2 * (a * b : Nat) * gaugeDualCoupling beta := by
  have hbound := (cubicalXYWilsonFreeEnergy_mem_Icc ha hb hc k
    (fun _ : CubicalPlaquette a b c => beta) (fun _ => hbeta)).2
  have hdual := gaugeDualCoupling_pos hbeta
  simpa [abs_of_pos hdual, Finset.sum_const, nsmul_eq_mul, mul_assoc] using hbound

end
end StatMech.FrontierA
