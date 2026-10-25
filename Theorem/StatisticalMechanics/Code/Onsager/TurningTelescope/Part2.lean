/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix
import Def.StatisticalMechanics.Code.Onsager.TurningTelescope.Part2


namespace StatMech.Onsager

theorem ons_turnZ_telescope (n : ℕ) (d : Fin (n + 1) → Fin 4) :
    (∑ k : Fin n, ((d k.succ : ZMod 4) - (d k.castSucc : ZMod 4)))
      = (d (Fin.last n) : ZMod 4) - (d 0 : ZMod 4) := by
  
  set F : ℕ → ZMod 4 := fun i => if h : i < n + 1 then (d ⟨i, h⟩ : ZMod 4) else 0 with hF
  have hFval : ∀ (i : ℕ) (hi : i < n + 1), F i = (d ⟨i, hi⟩ : ZMod 4) := by
    intro i hi; rw [hF, dite_eq_left hi]
  have hsucc : ∀ k : Fin n, (d k.succ : ZMod 4) = F (k.val + 1) := by
    intro k
    have hk : k.val + 1 < n + 1 := by omega
    have he : k.succ = (⟨k.val + 1, hk⟩ : Fin (n + 1)) := by ext; simp
    rw [hFval (k.val + 1) hk, he]
  have hcast : ∀ k : Fin n, (d k.castSucc : ZMod 4) = F k.val := by
    intro k
    have hk : k.val < n + 1 := by omega
    have he : k.castSucc = (⟨k.val, hk⟩ : Fin (n + 1)) := by ext; simp
    rw [hFval k.val hk, he]
  have hstep : (∑ k : Fin n, ((d k.succ : ZMod 4) - (d k.castSucc : ZMod 4)))
      = ∑ k : Fin n, (F (k.val + 1) - F k.val) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hsucc k, hcast k]
    rfl
  have heN : (Fin.last n) = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by ext; simp
  have he0 : (0 : Fin (n + 1)) = (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) := by ext; simp
  rw [hstep, Fin.sum_univ_eq_sum_range (fun i => F (i + 1) - F i) n,
    Finset.sum_range_sub F n, hFval n (Nat.lt_succ_self n), hFval 0 (Nat.succ_pos n),
    heN, he0]
  rfl


end StatMech.Onsager
