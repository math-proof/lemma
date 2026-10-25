/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.Onsager.ChordCut.Part2


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


theorem stopEvent_exists (D : BoxData) (w : Pt) (hw : w ∈ D.B) :
    ∃ k, stopEvent D w k := by
  refine ⟨(D.x1 - w.1 + 1).toNat, ?_, Or.inr ?_⟩
  · have : 1 ≤ D.x1 - w.1 + 1 := by have := D.hx1 w hw; omega
    omega
  · have hle := D.hx1 w hw
    have : ((D.x1 - w.1 + 1).toNat : ℤ) = D.x1 - w.1 + 1 := by
      rw [Int.toNat_of_nonneg]; omega
    omega


theorem chord_firstHit (D : BoxData) (w : Pt) (hw : w ∈ D.B) :
    ∃ k : ℕ, 1 ≤ k ∧ (rayX w k ∈ D.B ∨ D.x1 < w.1 + (k : ℤ)) ∧
      (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B ∧ w.1 + (j : ℤ) ≤ D.x1) := by
  classical
  have hex : ∃ k, stopEvent D w k := stopEvent_exists D w hw
  refine ⟨Nat.find hex, ?_, ?_, ?_⟩
  · exact (Nat.find_spec hex).1
  · exact (Nat.find_spec hex).2
  · intro j hj1 hjk
    have hnot : ¬ stopEvent D w j := Nat.find_min hex hjk
    simp only [stopEvent, not_and, not_or, not_lt] at hnot
    have := hnot hj1
    exact ⟨this.1, this.2⟩


end StatMech.Onsager.ChordCut
