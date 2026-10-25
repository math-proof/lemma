/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
import Theorem.StatisticalMechanics.Code.FK.Uniqueness
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace


section Abstract

variable {Ω : Type*} [MeasurableSpace Ω]


theorem dlr_sandwich_unique {free wired phi : Measure Ω} {A : Set Ω}
    (hsand : free.real A ≤ phi.real A ∧ phi.real A ≤ wired.real A)
    (hfw : free.real A = wired.real A) :
    phi.real A = free.real A ∧ phi.real A = wired.real A := by
  obtain ⟨h1, h2⟩ := hsand
  
  rw [hfw] at h1
  have heqw : phi.real A = wired.real A := le_antisymm h2 h1
  exact ⟨by rw [heqw, hfw], heqw⟩


theorem sandwich_eq_of_free_eq_wired {free wired phi : Measure Ω} {P : Set Ω → Prop}
    (hsand : ∀ A, P A → free.real A ≤ phi.real A ∧ phi.real A ≤ wired.real A)
    (hfw : ∀ A, P A → free.real A = wired.real A) :
    ∀ A, P A → phi.real A = free.real A ∧ phi.real A = wired.real A :=
  fun A hA => dlr_sandwich_unique (hsand A hA) (hfw A hA)


theorem countable_density_ne {a b : ℝ → ℝ} (hb : Monotone b)
    (heq_at_cont : ∀ p, ContinuousAt b p → a p = b p) :
    {p : ℝ | a p ≠ b p}.Countable := by
  refine (hb.countable_not_continuousAt).mono ?_
  intro p hp
  simp only [mem_setOf_eq] at hp ⊢
  exact fun hcont => hp (heq_at_cont p hcont)


theorem fk_uniqueness_off_countable_abstract
    (free wired : ℝ → Measure Ω) (P : Set Ω → Prop) (a b : ℝ → ℝ)
    (hb : Monotone b)
    (heq_at_cont : ∀ p, ContinuousAt b p → a p = b p)
    (hcrit : ∀ p, a p = b p → ∀ A, P A → (free p).real A = (wired p).real A) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ phi : Measure Ω,
        (∀ A, P A → (free p).real A ≤ phi.real A ∧ phi.real A ≤ (wired p).real A) →
          ∀ A, P A → phi.real A = (free p).real A ∧ phi.real A = (wired p).real A := by
  
  refine ⟨{p : ℝ | a p ≠ b p}, countable_density_ne hb heq_at_cont, ?_⟩
  intro p hp phi hsand A hA
  
  simp only [mem_setOf_eq, not_not] at hp
  have hfw : ∀ A, P A → (free p).real A = (wired p).real A := hcrit p hp
  
  exact sandwich_eq_of_free_eq_wired hsand hfw A hA

end Abstract
end FK
end StatMech
