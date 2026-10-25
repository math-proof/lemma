/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Def.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation


namespace StatMech.Onsager

open BigOperators

theorem ons_reversibleTurnMatrix_surgery_sign
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    ons_loopWeight (ons_reversibleTurnMatrix dir omega q)
        (ons_surgery e rev loop) =
      -ons_loopWeight (ons_reversibleTurnMatrix dir omega q) loop := by
  unfold ons_loopWeight ons_reversibleTurnMatrix
  simp_rw [Finset.prod_mul_distrib]
  rw [ons_reversibleFactorProduct_surgery rev hrev dir hdir q hq e loop hloop,
    ons_turnProduct_surgery_sign rev hrev dir hdir omega homega hI e loop hloop]
  ring


theorem ons_reversibleTurnMatrix_lemma5
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (hrne : rev e ≠ e) :
    ∑ loop ∈ ons_loopSetBoth (n := n) e (rev e),
        ons_loopWeight (ons_reversibleTurnMatrix dir omega q) loop = 0 := by
  apply ons_lemma5 _ e rev hrev hrne
  intro loop hloop
  apply ons_reversibleTurnMatrix_surgery_sign
      rev hrev dir hdir omega homega hI q hq e loop
  simpa only [ons_mem_loopSetBoth] using hloop


theorem ons_invariantStateProduct_surgery
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (weight : E → ℂ) (hweight : ∀ x, weight (rev x) = weight x)
    (e : E) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    (∏ k, weight (ons_surgery e rev loop k)) =
      ∏ k, weight (loop k) := by
  let l := ons_l e rev loop
  let m := ons_m e rev loop
  have hlm : l ≤ m := ons_l_le_m hrev hloop
  let surgery := ons_surgery e rev loop
  have hs : surgery = ons_revSeg rev l m loop :=
    ons_surgery_eq_revSeg hloop
  let U : Finset (Fin n) :=
    Finset.univ.filter (fun k ↦ l ≤ k ∧ k ≤ m)
  let P : ℂ := ∏ k ∈ U, weight (loop k)
  have hmirror : (∏ k ∈ U, weight (loop (ons_mir l m k))) = P := by
    rw [show P = ∏ k ∈ U, weight (loop k) from rfl]
    refine Finset.prod_bij'
      (fun k _ ↦ ons_mir l m k) (fun k _ ↦ ons_mir l m k)
      ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      change ons_mir l m k ∈ U
      simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using
        ons_mir_mem hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      change ons_mir l m k ∈ U
      simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using
        ons_mir_mem hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact ons_mir_mir hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact ons_mir_mir hk'.1 hk'.2
    · intro k _
      rfl
  have hinside : (∏ k ∈ U, weight (surgery k)) = P := by
    calc
      (∏ k ∈ U, weight (surgery k)) =
          ∏ k ∈ U, weight (loop (ons_mir l m k)) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [show U = Finset.univ.filter (fun k ↦ l ≤ k ∧ k ≤ m) from rfl,
          Finset.mem_filter] at hk
        have hsk : surgery k = rev (loop (ons_mir l m k)) := by
          rw [hs]
          exact ons_revSeg_inside rev loop hk.2.1 hk.2.2
        rw [hsk, hweight]
      _ = P := hmirror
  have houtside :
      (∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k ≤ m)),
          weight (surgery k)) =
        ∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k ≤ m)),
          weight (loop k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    have hsk : surgery k = loop k := by
      rw [hs]
      exact ons_revSeg_outside rev loop hk.2
    rw [hsk]
  calc
    (∏ k, weight (surgery k)) =
        (∏ k ∈ U, weight (surgery k)) *
          ∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k ≤ m)),
            weight (surgery k) := by
      rw [show U = Finset.univ.filter (fun k ↦ l ≤ k ∧ k ≤ m) from rfl,
        Finset.prod_filter_mul_prod_filter_not]
    _ = P * ∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k ≤ m)),
          weight (loop k) := by rw [hinside, houtside]
    _ = ∏ k, weight (loop k) := by
      rw [show P = ∏ k ∈ U, weight (loop k) from rfl,
        show U = Finset.univ.filter (fun k ↦ l ≤ k ∧ k ≤ m) from rfl,
        Finset.prod_filter_mul_prod_filter_not]


end StatMech.Onsager
