/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Inequalities.Pivotal.Part2


namespace StatMech

open ConfigSpace Function

variable {E : Type*} [DecidableEq E]


lemma isPivotal_comm (e : E) (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    IsPivotal e A ω ↔ (setClosed e ω ∈ A) ≠ (setOpen e ω ∈ A) :=
  ⟨fun h => h.symm, fun h => h.symm⟩


lemma isPivotal_congr {e : E} {A : Set (ConfigSpace E)} {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : IsPivotal e A ω ↔ IsPivotal e A ω' := by
  unfold IsPivotal
  rw [setOpen_congr h, setClosed_congr h]


@[simp] lemma isPivotal_setOpen (e : E) (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    IsPivotal e A (setOpen e ω) ↔ IsPivotal e A ω := by
  unfold IsPivotal; rw [setOpen_setOpen, setClosed_setOpen]


@[simp] lemma isPivotal_setClosed (e : E) (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    IsPivotal e A (setClosed e ω) ↔ IsPivotal e A ω := by
  unfold IsPivotal; rw [setOpen_setClosed, setClosed_setClosed]


theorem isPivotal_iff_of_isIncreasing {e : E} {A : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (ω : ConfigSpace E) :
    IsPivotal e A ω ↔ (setClosed e ω ∉ A ∧ setOpen e ω ∈ A) := by
  have hle : setClosed e ω ≤ setOpen e ω := setClosed_le_setOpen e ω
  unfold IsPivotal
  constructor
  · intro h
    by_cases hc : setClosed e ω ∈ A
    · 
      exact absurd (h.symm) (by simp [hc, hA hle hc])
    · refine ⟨hc, ?_⟩
      by_contra ho
      exact h (by simp [hc, ho])
  · rintro ⟨hc, ho⟩
    simp [hc, ho]

end StatMech
