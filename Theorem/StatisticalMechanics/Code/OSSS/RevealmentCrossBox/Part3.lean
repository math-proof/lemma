/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part2
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


omit [Fintype E] [DecidableEq E] in

theorem reach0Inv_xbStep (endU endV : E → V) (ω : ConfigSpace E) (o : V) (s : XState V) (e : E)
    (hInv : reach0Inv endU endV ω o s) :
    reach0Inv endU endV ω o (xbStep endU endV o s e (ω e)) := by
  intro x hx
  rw [snd_xbStep_eq] at hx
  by_cases ho : o ∈ geomStep endU endV s.1 e (ω e)
  · rw [if_pos ho] at hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ReachOpen.refl x
    · by_cases hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
      · rw [if_pos hc] at hx
        rw [Finset.mem_insert, Finset.mem_insert] at hx
        obtain ⟨hopen, hend⟩ := hc
        rcases hx with rfl | rfl | hx
        · rcases hend with hU | hV
          · exact hInv _ hU
          · exact ReachOpen.step e hopen (Or.inl ⟨rfl, rfl⟩) (hInv _ hV)
        · rcases hend with hU | hV
          · exact ReachOpen.step e hopen (Or.inr ⟨rfl, rfl⟩) (hInv _ hU)
          · exact hInv _ hV
        · exact hInv _ hx
      · rw [if_neg hc] at hx; exact hInv _ hx
  · rw [if_neg ho] at hx; simp only [id] at hx
    by_cases hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc] at hx
      rw [Finset.mem_insert, Finset.mem_insert] at hx
      obtain ⟨hopen, hend⟩ := hc
      rcases hx with rfl | rfl | hx
      · rcases hend with hU | hV
        · exact hInv _ hU
        · exact ReachOpen.step e hopen (Or.inl ⟨rfl, rfl⟩) (hInv _ hV)
      · rcases hend with hU | hV
        · exact ReachOpen.step e hopen (Or.inr ⟨rfl, rfl⟩) (hInv _ hU)
        · exact hInv _ hV
      · exact hInv _ hx
    · rw [if_neg hc] at hx; exact hInv _ hx

omit [Fintype E] [DecidableEq E] in

theorem reach0Inv_runState (endU endV : E → V) (ω : ConfigSpace E) (o : V)
    (l : List E) (s : XState V) (hInv : reach0Inv endU endV ω o s) :
    reach0Inv endU endV ω o (runState (xbGuard endU endV) (xbStep endU endV o) ω l s) := by
  induction l generalizing s with
  | nil => simpa [runState] using hInv
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]; exact ih _ (reach0Inv_xbStep endU endV ω o s e hInv)
      · rw [if_neg hg]; exact ih s hInv


end OSSS
end StatMech
