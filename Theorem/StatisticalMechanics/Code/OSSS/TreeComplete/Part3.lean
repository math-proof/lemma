/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Def.StatisticalMechanics.Code.OSSS.TreeComplete.Part2
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace TreeComplete

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]

omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem mem_of_reachOpen_of_saturated (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (D : Finset V) (hsat : Saturated endU endV ω l D)
    (hl : ∀ e, e ∈ l) {x b : V} (h : ReachOpen endU endV ω x b) (hb : b ∈ D) : x ∈ D := by
  induction h with
  | refl x => exact hb
  | step e hopen hxy _ ih =>
      
      have hyD : _ := ih hb
      rcases hxy with ⟨hU, hV⟩ | ⟨hU, hV⟩
      · 
        have : endU e ∈ D ∧ endV e ∈ D :=
          hsat e (hl e) hopen (Or.inr (hV ▸ hyD))
        exact hU ▸ this.1
      · 
        have : endU e ∈ D ∧ endV e ∈ D :=
          hsat e (hl e) hopen (Or.inl (hU ▸ hyD))
        exact hV ▸ this.2

omit [Fintype E] [DecidableEq E] in


theorem saturated_of_fixpoint (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (D : Finset V)
    (hfix : runState (geomGuard endU endV) (geomStep endU endV) ω l D = D) :
    Saturated endU endV ω l D := by
  intro e he hopen hend
  have h := mem_runState_of_open_edge endU endV ω l D e he hopen hend
  rw [hfix] at h
  exact h

omit [Fintype E] [DecidableEq E] in

theorem runState_append (endU endV : E → V) (ω : ConfigSpace E)
    (l₁ l₂ : List E) (disc : Finset V) :
    runState (geomGuard endU endV) (geomStep endU endV) ω (l₁ ++ l₂) disc
      = runState (geomGuard endU endV) (geomStep endU endV) ω l₂
          (runState (geomGuard endU endV) (geomStep endU endV) ω l₁ disc) := by
  induction l₁ generalizing disc with
  | nil => simp [runState]
  | cons e rest ih =>
      simp only [List.cons_append, runState]
      by_cases hg : geomGuard endU endV disc e = true
      · rw [if_pos hg, if_pos hg]; exact ih _
      · rw [if_neg hg, if_neg hg]; exact ih _


end TreeComplete
end OSSS
end StatMech
