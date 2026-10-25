/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Theorem.StatisticalMechanics.Code.Walls.dg2degree.Part5
import Def.StatisticalMechanics.Code.Walls.npjnopinch
open SimpleGraph Set


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


theorem npj_lift_walk (S : Set (Site 2)) {x y : S}
    (p : ((hypercubicLattice 2).induce S).Walk x y) :
    ∃ w : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2), ∀ z ∈ w.support, z ∈ S := by
  induction p with
  | nil =>
      exact ⟨Walk.nil, by
        intro z hz
        simp only [Walk.support_nil, List.mem_singleton] at hz
        subst hz; exact Subtype.property _⟩
  | @cons a b c hab p ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨Walk.cons hab w, ?_⟩
      intro z hz
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Subtype.property _
      · exact hw z hz


theorem npj_ambient_walk_of_induce_reachable {S : Set (Site 2)} {x y : Site 2}
    (hx : x ∈ S) (hy : y ∈ S)
    (h : ((hypercubicLattice 2).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ w : (hypercubicLattice 2).Walk x y, ∀ z ∈ w.support, z ∈ S := by
  obtain ⟨p⟩ := h
  exact npj_lift_walk S p


theorem npj_paths_of_diagSplit {K : Set (Site 2)} (a b : ℤ)
    (hK : ((hypercubicLattice 2).induce K).Connected)
    (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
    (h00 : npj_c00 a b ∈ K) (h11 : npj_c11 a b ∈ K)
    (h10 : npj_c10 a b ∈ (Kᶜ : Set (Site 2))) (h01 : npj_c01 a b ∈ (Kᶜ : Set (Site 2))) :
    (∃ w : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b),
        ∀ z ∈ w.support, z ∈ K) ∧
    (∃ w : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b),
        ∀ z ∈ w.support, z ∈ (Kᶜ : Set (Site 2))) := by
  refine ⟨npj_ambient_walk_of_induce_reachable h00 h11 (hK.preconnected ⟨_, h00⟩ ⟨_, h11⟩),
          npj_ambient_walk_of_induce_reachable h10 h01 (hKc.preconnected ⟨_, h10⟩ ⟨_, h01⟩)⟩


theorem npj_noPinch_primary_of_separatingSide {K : Set (Site 2)} (a b : ℤ)
    {wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b)}
    (hwK : ∀ z ∈ wK.support, z ∈ K)
    {wKc : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b)}
    (hwKc : ∀ z ∈ wKc.support, z ∈ (Kᶜ : Set (Site 2)))
    (hsep : jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support}
              {npj_c10 a b} {npj_c01 a b}) :
    False := by
  obtain ⟨z, hzKc, hzK⟩ :=
    jcu_separatingSide_forces_cross hsep (rfl : npj_c10 a b ∈ ({npj_c10 a b} : Set _))
      (rfl : npj_c01 a b ∈ ({npj_c01 a b} : Set _)) wKc (fun z _ => Set.mem_univ z)
  
  exact (hwKc z hzKc) (hwK z hzK)


end Walls
end StatMech
