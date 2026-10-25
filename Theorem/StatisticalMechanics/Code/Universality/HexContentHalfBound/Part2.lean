/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Def.StatisticalMechanics.Code.Universality.HexContentHalfBound


namespace StatMech.Universality

open scoped BigOperators

noncomputable section

theorem hchb_find_eq_some_of_mem
    {l : List HexBridge}
    (hl : l.Pairwise (fun b c => b.width > c.width))
    {b : HexBridge} (hb : b ∈ l) :
    l.find? (fun c => decide (c.width = b.width)) = some b := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
      rw [List.pairwise_cons] at hl
      rcases List.mem_cons.mp hb with rfl | hb
      · simp
      · have hne : a.width ≠ b.width := by
          intro heq
          have hab := hl.1 b hb
          omega
        simp only [List.find?, decide_eq_true_eq, hne, Bool.false_eq_true,
          ↓reduceIte]
        exact ih hl.2 hb


theorem hchb_find_eq_some_iff (s : HexHWContentHalf) (T : ℕ)
    (b : HexBridge) :
    hchb_find s T = some b ↔ b ∈ s.1 ∧ b.width = T := by
  constructor
  · intro h
    have h' := h
    unfold hchb_find at h'
    have hp : decide (b.width = T) = true :=
      @List.find?_some HexBridge (fun c => decide (c.width = T)) b s.1 h'
    exact ⟨List.mem_of_find?_eq_some h',
      of_decide_eq_true hp⟩
  · rintro ⟨hb, rfl⟩
    exact hchb_find_eq_some_of_mem s.2 hb


end
end StatMech.Universality
