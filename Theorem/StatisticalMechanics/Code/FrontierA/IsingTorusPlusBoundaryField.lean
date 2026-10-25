/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusPlusBoundaryField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part8
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

open StatMech.Percolation

noncomputable section

variable {d k R : Nat}


theorem mk_mem_plusBoundaryEdges_iff (S : Finset (Site d)) (a b : Site d) :
    s(a, b) ∈ plusBoundaryEdges S ↔
      (hypercubicLattice d).Adj a b ∧
        ((a ∈ S ∧ b ∉ S) ∨ (a ∉ S ∧ b ∈ S)) := by
  classical
  constructor
  · intro h
    rw [plusBoundaryEdges, Finset.mem_filter] at h
    have htouch := h.1
    have hendpoint := gvBondTouch_endpoint htouch
    have hadj : (hypercubicLattice d).Adj a b := by
      rw [gvBondTouch, Finset.mem_image] at htouch
      obtain ⟨p, hp, he⟩ := htouch
      rw [Finset.mem_filter] at hp
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp.2.1
      · exact hp.2.1.symm
    refine ⟨hadj, ?_⟩
    rcases hendpoint with ha | hb
    · left
      refine ⟨ha, ?_⟩
      intro hb
      exact h.2 (fun v hv ↦ by
        rw [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl <;> assumption)
    · right
      refine ⟨?_, hb⟩
      intro ha
      exact h.2 (fun v hv ↦ by
        rw [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl <;> assumption)
  · rintro ⟨hab, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
    · rw [plusBoundaryEdges, Finset.mem_filter]
      constructor
      · rw [gvBondTouch, Finset.mem_image]
        refine ⟨(a, b), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨?_, ?_⟩, hab, Or.inl ha⟩
        · rw [gvCand, Finset.mem_biUnion]
          exact ⟨a, ha, gv_self_mem_ball a⟩
        · rw [gvCand, Finset.mem_biUnion]
          exact ⟨a, ha, gv_nbr_mem_ball hab⟩
      · intro hins
        exact hb (hins b (Sym2.mem_mk_right a b))
    · rw [plusBoundaryEdges, Finset.mem_filter]
      constructor
      · rw [gvBondTouch, Finset.mem_image]
        refine ⟨(a, b), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨?_, ?_⟩, hab, Or.inr hb⟩
        · rw [gvCand, Finset.mem_biUnion]
          exact ⟨b, hb, gv_nbr_mem_ball hab.symm⟩
        · rw [gvCand, Finset.mem_biUnion]
          exact ⟨b, hb, gv_self_mem_ball b⟩
      · intro hins
        exact ha (hins a (Sym2.mem_mk_left a b))


theorem exists_latticeNeighbor_lift_of_torusAdj (x : Site d)
    (z : IsingDyadicTorus d k)
    (h : (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) z) :
    ∃ y : Site d, (hypercubicLattice d).Adj x y ∧
      isingSiteToDyadicTorus k y = z := by
  rw [isingTorusGraph_adj_iff] at h
  rcases h with ⟨i, h | h⟩
  · refine ⟨coordShift x i (stepSign true), adj_coordShift x i true, ?_⟩
    rw [isingSiteToDyadicTorus_coordShift]
    simpa using h.symm
  · refine ⟨coordShift x i (stepSign false), adj_coordShift x i false, ?_⟩
    rw [isingSiteToDyadicTorus_coordShift]
    simp only [Bool.false_eq_true, if_false]
    rw [h]
    abel


end
end StatMech.FrontierA
