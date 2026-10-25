/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem reach_restrictCompl_le (m : Current V) (S : Finset V) {u v : V}
    (hr : (currentSubgraph G (restrictTo m Sᶜ)).Reachable u v) :
    (currentSubgraph G m).Reachable u v := by
  refine hr.mono ?_
  intro x y h
  refine ⟨h.1, ?_⟩
  have hxy := h.2
  simp only [restrictTo_apply] at hxy
  by_cases hc : edgeInside Sᶜ s(x, y)
  · rw [if_pos hc] at hxy; exact hxy
  · rw [if_neg hc] at hxy; omega


theorem reach_forward (m : Current V) (S : Finset V) (hn : NoCrossing G m S) (u v : V)
    (hu : u ∉ S) (hr : (currentSubgraph G m).Reachable u v) :
    (currentSubgraph G (restrictTo m Sᶜ)).Reachable u v ∧ v ∉ S := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact ⟨Reachable.refl _, hu⟩
  | @cons a b c hadj rest ih =>
    have ha : a ∉ S := hu
    have hab_adj : G.Adj a b := hadj.1
    have hab_pos : 1 ≤ m s(a, b) := hadj.2
    have he : s(a, b) ∈ G.edgeFinset := by rw [mem_edgeFinset]; exact hab_adj
    rcases hn _ he hab_pos with hins | hinc
    · exact absurd (hins a (by rw [Sym2.mem_iff]; left; rfl)) ha
    · have hbnotS : b ∉ S := by
        have hbc := hinc b (by rw [Sym2.mem_iff]; right; rfl)
        rw [Finset.mem_compl] at hbc; exact hbc
      obtain ⟨hrest, hvnotS⟩ := ih hbnotS
      refine ⟨Reachable.trans ?_ hrest, hvnotS⟩
      refine Adj.reachable ⟨hab_adj, ?_⟩
      simp only [restrictTo_apply]; rw [if_pos hinc]; exact hab_pos


theorem currentConnected_iff_compl (m : Current V) (S : Finset V) (hn : NoCrossing G m S)
    (u v : V) (hu : u ∉ S) :
    CurrentConnected G m u v ↔ CurrentConnected G (restrictTo m Sᶜ) u v :=
  ⟨fun h => (reach_forward G m S hn u v hu h).1, fun h => reach_restrictCompl_le G m S h⟩


theorem not_currentConnected_in_S (m : Current V) (S : Finset V) (hn : NoCrossing G m S)
    (g : V) (hg : g ∉ S) (v : V) (hv : v ∈ S) :
    ¬ CurrentConnected G m g v := fun h => (reach_forward G m S hn g v hg h).2 hv


end Sharpness
end StatMech
