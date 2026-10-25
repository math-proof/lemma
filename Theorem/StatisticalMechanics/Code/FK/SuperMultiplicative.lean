/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

section Reach

variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)


theorem fsm_reach_inl_inl (a b : V) :
    (G ⊕g H).Reachable (Sum.inl a) (Sum.inl b) ↔ G.Reachable a b := by
  constructor
  · intro h
    rw [reachable_eq_reflTransGen] at h ⊢
    have key : ∀ x, Relation.ReflTransGen (G ⊕g H).Adj (Sum.inl a) x →
        ∃ a', x = Sum.inl a' ∧ Relation.ReflTransGen G.Adj a a' := by
      intro x hx
      induction hx with
      | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
      | @tail y z hprev hadj ih =>
        obtain ⟨a', rfl, hra'⟩ := ih
        match z, hadj with
        | Sum.inl c', hadj => exact ⟨c', rfl, hra'.tail (by simpa using hadj)⟩
        | Sum.inr c', hadj => simp at hadj
    obtain ⟨a', haeq, hra'⟩ := key (Sum.inl b) h
    cases haeq; exact hra'
  · rintro ⟨p⟩; exact ⟨p.map Embedding.sumInl.toHom⟩


theorem fsm_reach_inr_inr (a b : W) :
    (G ⊕g H).Reachable (Sum.inr a) (Sum.inr b) ↔ H.Reachable a b := by
  constructor
  · intro h
    rw [reachable_eq_reflTransGen] at h ⊢
    have key : ∀ x, Relation.ReflTransGen (G ⊕g H).Adj (Sum.inr a) x →
        ∃ a', x = Sum.inr a' ∧ Relation.ReflTransGen H.Adj a a' := by
      intro x hx
      induction hx with
      | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
      | @tail y z hprev hadj ih =>
        obtain ⟨a', rfl, hra'⟩ := ih
        match z, hadj with
        | Sum.inr c', hadj => exact ⟨c', rfl, hra'.tail (by simpa using hadj)⟩
        | Sum.inl c', hadj => simp at hadj
    obtain ⟨a', haeq, hra'⟩ := key (Sum.inr b) h
    cases haeq; exact hra'
  · rintro ⟨p⟩; exact ⟨p.map Embedding.sumInr.toHom⟩


theorem fsm_not_reach_inl_inr (a : V) (b : W) :
    ¬ (G ⊕g H).Reachable (Sum.inl a) (Sum.inr b) := by
  intro h
  rw [reachable_eq_reflTransGen] at h
  have key : ∀ x, Relation.ReflTransGen (G ⊕g H).Adj (Sum.inl a) x → ∃ a', x = Sum.inl a' := by
    intro x hx
    induction hx with
    | refl => exact ⟨a, rfl⟩
    | @tail y z hprev hadj ih =>
      obtain ⟨a', rfl⟩ := ih
      match z, hadj with
      | Sum.inl c', hadj => exact ⟨c', rfl⟩
      | Sum.inr c', hadj => simp at hadj
  obtain ⟨a', haeq⟩ := key (Sum.inr b) h
  exact Sum.inr_ne_inl haeq

end Reach
end FK
end StatMech
