/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc17menger.Part4
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]

variable {G : SimpleGraph V}


theorem bc18_firstHit {S : Set V} {a b : V} (p : G.Walk a b) :
    (∃ z ∈ p.support, z ∈ S) →
    ∃ (c : V) (q : G.Walk a c), c ∈ S ∧ q.support ⊆ p.support ∧
      (∀ z ∈ q.support, z ∈ S → z = c) := by
  induction p with
  | nil =>
      rintro ⟨z, hz, hzS⟩
      rw [Walk.support_nil, List.mem_singleton] at hz
      subst hz
      exact ⟨z, Walk.nil, hzS, fun w hw => hw, fun w hw _ => by
        rw [Walk.support_nil, List.mem_singleton] at hw; exact hw⟩
  | cons hadj t ih =>
      rename_i u v w
      intro hmem
      by_cases huS : u ∈ S
      · exact ⟨u, Walk.nil, huS, by
          intro z hz; rw [Walk.support_nil, List.mem_singleton] at hz; subst hz
          exact Walk.start_mem_support _,
          fun z hz _ => by rw [Walk.support_nil, List.mem_singleton] at hz; exact hz⟩
      · have hmem' : ∃ z ∈ t.support, z ∈ S := by
          obtain ⟨z, hz, hzS⟩ := hmem
          rw [Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact absurd hzS huS
          · exact ⟨z, hz, hzS⟩
        obtain ⟨c, q, hcS, hqsub, hq⟩ := ih hmem'
        refine ⟨c, Walk.cons hadj q, hcS, ?_, ?_⟩
        · intro z hz
          rw [Walk.support_cons, List.mem_cons] at hz ⊢
          rcases hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (hqsub hz)
        · intro z hz hzS
          rw [Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact absurd hzS huS
          · exact hq z hz hzS


theorem bc18_firstHitPath {S : Set V} {a b : V} (p : G.Walk a b)
    (hmem : ∃ z ∈ p.support, z ∈ S) :
    ∃ (c : V) (q : G.Walk a c), q.IsPath ∧ c ∈ S ∧ q.support ⊆ p.support ∧
      (∀ z ∈ q.support, z ∈ S → z = c) := by
  obtain ⟨c, q, hcS, hqsub, hq⟩ := bc18_firstHit p hmem
  refine ⟨c, q.bypass, q.bypass_isPath, hcS, fun z hz => hqsub (q.support_bypass_subset hz),
    fun z hz hzS => hq z (q.support_bypass_subset hz) hzS⟩


end StatMech.Walls
