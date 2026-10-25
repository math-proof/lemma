/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Def.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part3


namespace StatMech.Onsager

open BigOperators

theorem ons_involutiveLoopRev_involutive
    {E : Type*} {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (loop : Fin n → E) :
    ons_involutiveLoopRev rev (ons_involutiveLoopRev rev loop) = loop := by
  funext k
  simpa only [ons_involutiveLoopRev, neg_neg] using hrev (loop k)

theorem ons_visits_involutiveLoopRev
    {E : Type*} {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (loop : Fin n → E) (e : E) :
    (∃ i, ons_involutiveLoopRev rev loop i = e) ↔
      ∃ i, loop i = rev e := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨-i, ?_⟩
    have h := congrArg rev hi
    change rev (rev (loop (-i))) = rev e at h
    rw [hrev (loop (-i))] at h
    exact h
  · rintro ⟨i, hi⟩
    refine ⟨-i, ?_⟩
    simp only [ons_involutiveLoopRev, neg_neg, hi]
    exact hrev e

theorem ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (rowWeight colWeight : E → ℂ)
    (hweight : ∀ x,
      rowWeight (rev x) * colWeight (rev x) =
        rowWeight x * colWeight x)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (loop : Fin n → E) :
    ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q)
        (ons_involutiveLoopRev rev loop) =
      ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q) loop := by
  rw [ons_loopWeight_stateWeightedReversibleTurnMatrix,
    ons_loopWeight_stateWeightedReversibleTurnMatrix]
  have hstate :
      (∏ k, rowWeight (ons_involutiveLoopRev rev loop k) *
          colWeight (ons_involutiveLoopRev rev loop k)) =
        ∏ k, rowWeight (loop k) * colWeight (loop k) := by
    calc
      (∏ k, rowWeight (ons_involutiveLoopRev rev loop k) *
          colWeight (ons_involutiveLoopRev rev loop k)) =
          ∏ k, rowWeight (loop (-k)) * colWeight (loop (-k)) := by
        apply Finset.prod_congr rfl
        intro k hk
        exact hweight _
      _ = ∏ k, rowWeight (loop k) * colWeight (loop k) :=
        Equiv.prod_comp (Equiv.neg (Fin n))
          (fun k ↦ rowWeight (loop k) * colWeight (loop k))
  have hqprod :
      (∏ k, q (ons_involutiveLoopRev rev loop k)
          (ons_involutiveLoopRev rev loop (k + 1))) =
        ∏ k, q (loop k) (loop (k + 1)) := by
    calc
      (∏ k, q (ons_involutiveLoopRev rev loop k)
          (ons_involutiveLoopRev rev loop (k + 1))) =
          ∏ k, q (loop (-(k + 1))) (loop (-k)) := by
        apply Finset.prod_congr rfl
        intro k hk
        exact hq _ _
      _ = ∏ k, q (loop k) (loop (k + 1)) := by
        rw [← Equiv.prod_comp
          ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n)))
          (fun j ↦ q (loop j) (loop (j + 1)))]
        apply Finset.prod_congr rfl
        intro k hk
        have hrho :
            ((Equiv.addRight (1 : Fin n)).trans
              (Equiv.neg (Fin n))) k = -(k + 1) := rfl
        rw [hrho]
        have hk1 : (-(k + 1) + 1 : Fin n) = -k := by abel
        rw [hk1]
  have hturn :
      (∏ k, ons_turnW omega
          (dir (ons_involutiveLoopRev rev loop (k + 1)))
          (dir (ons_involutiveLoopRev rev loop k))) =
        ∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) := by
    calc
      (∏ k, ons_turnW omega
          (dir (ons_involutiveLoopRev rev loop (k + 1)))
          (dir (ons_involutiveLoopRev rev loop k))) =
          ∏ k, ons_turnW omega⁻¹
            (dir (loop (-k))) (dir (loop (-(k + 1)))) := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [ons_involutiveLoopRev, hdir]
        rw [ons_turnW_rev, ons_turnW_omega_inv]
      _ = ∏ k, ons_turnW omega⁻¹
          (dir (loop (k + 1))) (dir (loop k)) := by
        rw [← Equiv.prod_comp
          ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n)))
          (fun j ↦ ons_turnW omega⁻¹
            (dir (loop (j + 1))) (dir (loop j)))]
        apply Finset.prod_congr rfl
        intro k hk
        have hrho :
            ((Equiv.addRight (1 : Fin n)).trans
              (Equiv.neg (Fin n))) k = -(k + 1) := rfl
        rw [hrho]
        have hk1 : (-(k + 1) + 1 : Fin n) = -k := by abel
        rw [hk1]
      _ = _ := ons_cyclicTurnProduct_omega_inv omega homega hI
        (fun k ↦ dir (loop k))
  rw [hstate, hqprod, hturn]

end StatMech.Onsager
