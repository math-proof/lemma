/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterGhostLift.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned.Part2
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V]


theorem lpTwoGhostStarEdge_injective (side : W -> Bool) :
    Function.Injective ((fun x : W =>
      s(Sum.inl x, Sum.inr (side x))) :
        W -> Sym2 (LPTwoGhostVertex W)) := by
  intro x y h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · exact Sum.inl.inj h.1
  · exact absurd h.1 (by simp)

theorem lpTwoGhostBaseEdges_disjoint_star
    (E : Finset (Sym2 W)) (side : W -> Bool) :
    Disjoint (lpTwoGhostBaseEdges E) (lpTwoGhostStarEdges side) := by
  rw [Finset.disjoint_left]
  intro e he hs
  simp only [lpTwoGhostBaseEdges, lpTwoGhostStarEdges,
    Finset.mem_image, Finset.mem_univ, true_and] at he hs
  obtain ⟨e0, _, rfl⟩ := he
  obtain ⟨x, hx⟩ := hs
  induction e0 with
  | h a b =>
      rw [Sym2.map_mk, Sym2.eq_iff] at hx
      rcases hx with h | h <;> simp at h


end
end StatMech.Ising
