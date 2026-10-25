/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part5
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.TreeComplete

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


omit [Fintype E] in


theorem xbPass_fixpoint (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (disc₀ : Finset V) :
    xbPass endU endV o ω l
        ((xbPass endU endV o ω l)^[2 * (xbUniverse endU endV o l disc₀).card] (disc₀, ∅))
      = (xbPass endU endV o ω l)^[2 * (xbUniverse endU endV o l disc₀).card] (disc₀, ∅) := by
  set U := xbUniverse endU endV o l disc₀ with hU
  have hinfl1 : ∀ s : XState V, s.1 ⊆ (xbPass endU endV o ω l s).1 := by
    intro s; rw [xbPass, fst_runState_xbStep]; exact subset_runState endU endV ω l s.1
  have hinfl2 : ∀ s : XState V, s.2 ⊆ (xbPass endU endV o ω l s).2 := by
    intro s; exact subset_snd_runState endU endV o ω l s
  have hb1 : ∀ s : XState V, s.1 ⊆ U → s.2 ⊆ U → (xbPass endU endV o ω l s).1 ⊆ U := by
    intro s hs1 _
    rw [xbPass, fst_runState_xbStep]
    refine subset_trans (runState_subset_union endU endV ω l s.1) ?_
    rw [hU, xbUniverse]
    intro x hx; rw [Finset.mem_union] at hx
    rcases hx with hd | hep
    · exact hs1 hd
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hep)
  have hb2 : ∀ s : XState V, s.1 ⊆ U → s.2 ⊆ U → (xbPass endU endV o ω l s).2 ⊆ U := by
    intro s _ hs2
    rw [xbPass]
    refine subset_trans (snd_runState_subset endU endV o ω l s) ?_
    rw [hU, xbUniverse]
    intro x hx
    rw [Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (hd | hep) | ho
    · exact hs2 hd
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hep)
    · exact Finset.mem_union_right _ ho
  have h01 : ((disc₀, ∅) : XState V).1 ⊆ U := by
    rw [hU, xbUniverse]; exact subset_trans Finset.subset_union_left Finset.subset_union_left
  have h02 : ((disc₀, ∅) : XState V).2 ⊆ U := by simp
  exact pairFixpoint_iterate (xbPass endU endV o ω l) U hinfl1 hinfl2 hb1 hb2 (disc₀, ∅) h01 h02


end OSSS
end StatMech
