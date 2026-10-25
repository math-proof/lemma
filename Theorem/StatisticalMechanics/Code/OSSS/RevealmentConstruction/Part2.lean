/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Revealment.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part2
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace RevealmentConstruction

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] [DecidableEq E] in


theorem eval_buildTree {State : Type*} (guard : State → E → Bool)
    (step : State → E → Bool → State) (base : State → Bool) (ω : ConfigSpace E)
    (l : List E) (σ : State) :
    (buildTree guard step base l σ).eval ω = base (runState guard step ω l σ) := by
  induction l generalizing σ with
  | nil => rfl
  | cons e rest ih =>
      simp only [buildTree, runState]
      by_cases hg : guard σ e = true
      · rw [if_pos hg, if_pos hg]
        simp only [DecisionTree.eval]
        by_cases hb : ω e
        · rw [if_pos hb, hb]; exact ih (step σ e true)
        · rw [if_neg hb]; simp only [Bool.not_eq_true] at hb; rw [hb]; exact ih (step σ e false)
      · rw [if_neg hg, if_neg hg]; exact ih σ

omit [Fintype E] [DecidableEq E] in


theorem runState_inv {State : Type*} (guard : State → E → Bool)
    (step : State → E → Bool → State) (Inv : State → Prop) (ω : ConfigSpace E)
    (hstep : ∀ σ e, Inv σ → guard σ e = true → Inv (step σ e (ω e)))
    (l : List E) (σ : State) (hσ : Inv σ) : Inv (runState guard step ω l σ) := by
  induction l generalizing σ with
  | nil => exact hσ
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : guard σ e = true
      · rw [if_pos hg]; exact ih _ (hstep σ e hσ hg)
      · rw [if_neg hg]; exact ih σ hσ


end RevealmentConstruction
end OSSS
end StatMech
