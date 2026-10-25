/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.bc113boundaryforest
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem bc113_toB_witness (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) (v : V) :
    ∃ b, B b ∧ G.Reachable v b ∧ G.dist v b = bc113_toB G B v := by
  classical
  have hex : ∃ b, B b ∧ G.Reachable v b := hreach v
  have hne : (Finset.univ.filter (fun b => B b ∧ G.Reachable v b)).Nonempty := by
    obtain ⟨b, hb⟩ := hex
    exact ⟨b, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb⟩
  
  obtain ⟨b, hbmem, hbeq⟩ := Finset.exists_mem_eq_inf' hne (fun b => G.dist v b)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbmem
  refine ⟨b, hbmem.1, hbmem.2, ?_⟩
  simp only [bc113_toB, dif_pos hex]
  exact hbeq.symm


theorem bc113_toB_le (G : SimpleGraph V) (B : V → Prop) {v b : V}
    (hb : B b) (hr : G.Reachable v b) : bc113_toB G B v ≤ G.dist v b := by
  classical
  have hex : ∃ b, B b ∧ G.Reachable v b := ⟨b, hb, hr⟩
  simp only [bc113_toB, dif_pos hex]
  refine Finset.inf'_le _ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hb, hr⟩


theorem bc113_toB_eq_zero_of_mem (G : SimpleGraph V) (B : V → Prop) {v : V} (hv : B v) :
    bc113_toB G B v = 0 := by
  have := bc113_toB_le G B hv (SimpleGraph.Reachable.refl v)
  simpa using Nat.le_zero.mp (by simpa using this)


theorem bc113_toB_pos_of_not_mem (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {v : V} (hv : ¬ B v) : 0 < bc113_toB G B v := by
  classical
  rcases Nat.eq_zero_or_pos (bc113_toB G B v) with h0 | hpos
  · exfalso
    obtain ⟨b, hb, hr, hdeq⟩ := bc113_toB_witness G B hreach v
    rw [h0] at hdeq
    have : v = b := by
      by_contra hne
      have : 0 < G.dist v b := by
        apply Nat.pos_of_ne_zero
        rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]; exact ⟨hne, hr⟩
      omega
    exact hv (this ▸ hb)
  · exact hpos


theorem bc113_exists_parent (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {v : V} (hv : ¬ B v) :
    ∃ u, G.Adj v u ∧ bc113_toB G B u < bc113_toB G B v := by
  obtain ⟨b, hb, hr, hdeq⟩ := bc113_toB_witness G B hreach v
  have hvb : v ≠ b := fun h => hv (h ▸ hb)
  obtain ⟨u, hadj, hlt⟩ := bc113_exists_closer_neighbour G hr hvb
  refine ⟨u, hadj, ?_⟩
  
  have hru : G.Reachable u b := (hadj.symm.reachable).trans hr
  calc bc113_toB G B u ≤ G.dist u b := bc113_toB_le G B hb hru
    _ < G.dist v b := hlt
    _ = bc113_toB G B v := hdeq


end StatMech.Walls
