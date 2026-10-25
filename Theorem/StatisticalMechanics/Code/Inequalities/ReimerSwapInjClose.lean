/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in


theorem sameOrbit_iff_orbitKey (p q : ConfigSpace α × ConfigSpace α) :
    sameOrbit p q ↔ orbitKey p = orbitKey q := by
  constructor
  · intro h
    apply Prod.ext <;> funext a <;> rcases h a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [orbitKey, h1, h2, Bool.or_comm, Bool.and_comm]
  · intro h a
    have hor := congrFun (congrArg Prod.fst h) a
    have hand := congrFun (congrArg Prod.snd h) a
    simp only [orbitKey] at hor hand
    revert hor hand
    cases p.1 a <;> cases p.2 a <;> cases q.1 a <;> cases q.2 a <;> simp_all

omit [Fintype α] [DecidableEq α] in


theorem orbitKey_swapPair (σ : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : orbitKey (swapPair σ p) = orbitKey p := by
  apply Prod.ext <;> funext a <;>
    simp only [orbitKey, swapPair_fst, swapPair_snd, swapGlue_apply] <;>
    by_cases h : σ p a <;> simp [h, Bool.or_comm, Bool.and_comm]

omit [Fintype α] [DecidableEq α] in


theorem swapPair_eq_of_sameOrbit (p q : ConfigSpace α × ConfigSpace α) (h : sameOrbit p q) :
    q = swapPair (fun _ => fun a => decide (q.1 a ≠ p.1 a)) p := by
  apply Prod.ext
  · funext a
    simp only [swapPair_fst, swapGlue_apply]
    by_cases hpe : q.1 a = p.1 a
    · simp only [hpe, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    · simp only [ne_eq, hpe, not_false_eq_true, decide_true, if_true]
      rcases h a with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 hpe
      · exact h1
  · funext a
    simp only [swapPair_snd, swapGlue_apply]
    by_cases hpe : q.1 a = p.1 a
    · simp only [hpe, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      rcases h a with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · rw [h2, ← hpe, h1]
    · simp only [ne_eq, hpe, not_false_eq_true, decide_true, if_true]
      rcases h a with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1 hpe
      · exact h2


end StatMech
