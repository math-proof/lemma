/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeClassification
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decLoopScalar_sum_fixedExponent_two_bucket
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (d : ons_Dart L) (r : ℕ) (m : ons_DecEdge L →₀ ℕ) :
    (∑ loop : Fin (r + 1) → ons_Dart L,
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0) =
      2 * ons_decFormalFixedBucketE L a b d r m +
        ons_decFormalFixedBucketN L a b d r m := by
  let P : (Fin (r + 1) → ons_Dart L) → Prop :=
    fun loop ↦ ∃ k, loop k = d
  let Q : (Fin (r + 1) → ons_Dart L) → Prop :=
    fun loop ↦ ∃ k, loop k = ons_dartRev L d
  let f : (Fin (r + 1) → ons_Dart L) → ℂ := fun loop ↦
    if ons_decLoopExponent L loop = m then
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop
    else 0
  have hsplit := ons_sum_split_by_two P Q f
  have hboth := ons_decLoopScalar_sum_both_fixedExponent_eq_zero
    (n := r + 1) L a b d m
  have hbothset :
      Finset.univ.filter (fun loop : Fin (r + 1) → ons_Dart L ↦
        (∃ k, loop k = d) ∧ ∃ k, loop k = ons_dartRev L d) =
      ons_loopSetBoth (n := r + 1) d (ons_dartRev L d) := by
    ext loop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_mem_loopSetBoth]
  rw [← hbothset] at hboth
  have hsymm := ons_decLoopScalar_sum_one_orientation_symm
    (n := r + 1) L a b d m
  have hset :
      Finset.univ.filter (fun loop : Fin (r + 1) → ons_Dart L ↦
        (∃ k, loop k = ons_dartRev L d) ∧ ¬ ∃ k, loop k = d) =
      Finset.univ.filter (fun loop : Fin (r + 1) → ons_Dart L ↦
        (¬ ∃ k, loop k = d) ∧ ∃ k, loop k = ons_dartRev L d) := by
    ext loop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, f] at hsplit
  unfold ons_decFormalFixedBucketE ons_decFormalFixedBucketN
  linear_combination hsplit + hboth - hsymm

end StatMech.Onsager
