/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part3


namespace StatMech.Onsager

open Matrix BigOperators


theorem ons_revSeg_outside {E} {n : ℕ} [NeZero n] (rev : E → E) {l m : Fin n}
    (v : Fin n → E) {k : Fin n} (h : ¬ (l ≤ k ∧ k ≤ m)) :
    ons_revSeg rev l m v k = v k := by
  unfold ons_revSeg; rw [if_neg h]


theorem ons_revSeg_inside {E} {n : ℕ} [NeZero n] (rev : E → E) {l m : Fin n}
    (v : Fin n → E) {k : Fin n} (hlk : l ≤ k) (hkm : k ≤ m) :
    ons_revSeg rev l m v k = rev (v (ons_mir l m k)) := by
  unfold ons_revSeg; rw [if_pos ⟨hlk, hkm⟩]


theorem ons_revSeg_involutive {E} {n : ℕ} [NeZero n] {rev : E → E}
    (hrev : Function.Involutive rev) {l m : Fin n} (v : Fin n → E) :
    ons_revSeg rev l m (ons_revSeg rev l m v) = v := by
  funext k
  by_cases hk : l ≤ k ∧ k ≤ m
  · obtain ⟨hlk, hkm⟩ := hk
    rw [ons_revSeg_inside rev _ hlk hkm]
    obtain ⟨h1, h2⟩ := ons_mir_mem hlk hkm
    rw [ons_revSeg_inside rev _ h1 h2, ons_mir_mir hlk hkm, hrev]
  · rw [ons_revSeg_outside rev _ hk, ons_revSeg_outside rev _ hk]


end StatMech.Onsager
