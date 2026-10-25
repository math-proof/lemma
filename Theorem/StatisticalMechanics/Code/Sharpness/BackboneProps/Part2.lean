/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Def.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable {H : SimpleGraph V}


@[simp]
theorem removeWalk_apply {a b : V} (n : Current V) (p : H.Walk a b) (e : Sym2 V) :
    removeWalk n p e = n e - p.edges.count e := rfl


theorem incidentFlux_removeWalk {a b : V} (n : Current V) (p : H.Walk a b)
    (hsub : ∀ e ∈ p.edges, e ∈ G.edgeFinset)
    (hle : ∀ e ∈ G.edgeFinset, p.edges.count e ≤ n e) (x : V) :
    incidentFlux G (removeWalk n p) x = incidentFlux G n x - walkDeg p x := by
  unfold incidentFlux
  simp only [removeWalk_apply]
  rw [Finset.sum_tsub_distrib]
  · rw [sum_count_eq_walkDeg G p x hsub]
  · intro e he
    rw [Finset.mem_filter] at he
    exact hle e he.1


theorem sources_removeWalk_eq_empty {n : Current V} {a b : V}
    (p : IsBackbonePath G n a b) (hab : a ≠ b)
    (hsrc : sources G n = {a, b}) :
    sources G (removeWalk n p.1) = ∅ := by
  classical
  
  
  have hsub : ∀ e ∈ p.1.edges, e ∈ G.edgeFinset :=
    fun e he => isBackbonePath_edge_mem G p he
  have htrail : p.1.IsTrail := p.2.isTrail
  have hle : ∀ e ∈ G.edgeFinset, p.1.edges.count e ≤ n e := by
    intro e _
    by_cases hmem : e ∈ p.1.edges
    · calc p.1.edges.count e ≤ 1 := htrail.count_edges_le_one e
        _ ≤ n e := isBackbonePath_edge_pos G p hmem
    · rw [List.count_eq_zero_of_not_mem hmem]; exact Nat.zero_le _
  
  have hsrc_iff : ∀ x : V, Odd (incidentFlux G n x) ↔ (x = a ∨ x = b) := by
    intro x
    have : x ∈ sources G n ↔ x ∈ ({a, b} : Finset V) := by rw [hsrc]
    rw [mem_sources, Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_sources] at hx
  rw [incidentFlux_removeWalk G n p.1 hsub hle x] at hx
  
  
  have hwalk : Odd (walkDeg p.1 x) ↔ (x = a ∨ x = b) := by
    rw [walkDeg_odd_iff p.1 p.2 x]
    exact ⟨fun h => h.1, fun h => ⟨h, hab⟩⟩
  have hsame : Odd (incidentFlux G n x) ↔ Odd (walkDeg p.1 x) := by
    rw [hsrc_iff x, hwalk]
  
  have hge : walkDeg p.1 x ≤ incidentFlux G n x := by
    rw [← sum_count_eq_walkDeg G p.1 x hsub]
    unfold incidentFlux
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mem_filter] at he
    exact hle e he.1
  
  have heven : Even (incidentFlux G n x - walkDeg p.1 x) := by
    rw [Nat.even_sub hge, ← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even, hsame]
  exact (Nat.not_odd_iff_even.mpr heven) hx

end Sharpness
end StatMech
