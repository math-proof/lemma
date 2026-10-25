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
import Def.StatisticalMechanics.Code.OSSS.RevealmentConstruction
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


omit [Fintype E] in


theorem mem_queried_buildTree {State : Type*} (guard : State → E → Bool)
    (step : State → E → Bool → State) (base : State → Bool) (Inv : State → Prop)
    (ω : ConfigSpace E)
    (hstep : ∀ σ e, Inv σ → guard σ e = true → Inv (step σ e (ω e)))
    (l : List E) (σ : State) (hσ : Inv σ) (i : E)
    (hi : i ∈ (buildTree guard step base l σ).queried ω) :
    ∃ τ, Inv τ ∧ guard τ i = true := by
  induction l generalizing σ with
  | nil => simp [buildTree, DecisionTree.queried] at hi
  | cons e rest ih =>
      simp only [buildTree] at hi
      by_cases hg : guard σ e = true
      · rw [if_pos hg] at hi
        rw [DecisionTree.queried, Finset.mem_insert] at hi
        rcases hi with rfl | hi'
        · exact ⟨σ, hσ, hg⟩
        · by_cases hb : ω e
          · rw [if_pos hb] at hi'
            have hI := hstep σ e hσ hg; rw [hb] at hI
            exact ih (step σ e true) hI hi'
          · rw [if_neg hb] at hi'
            have hI := hstep σ e hσ hg
            simp only [Bool.not_eq_true] at hb; rw [hb] at hI
            exact ih (step σ e false) hI hi'
      · rw [if_neg hg] at hi
        exact ih σ hσ hi


end RevealmentConstruction
end OSSS
end StatMech
