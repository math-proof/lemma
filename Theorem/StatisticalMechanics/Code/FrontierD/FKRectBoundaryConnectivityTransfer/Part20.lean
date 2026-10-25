/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part22
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem walk_sum_inl_aux
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {a z : V ⊕ W} (p : (G.sum H).Walk a z) :
    ∀ u : V, a = Sum.inl u →
      ∃ v : V, z = Sum.inl v ∧ Nonempty (G.Walk u v) := by
  induction p with
  | nil =>
      intro u hu
      exact ⟨u, hu, ⟨.nil⟩⟩
  | @cons a b z hab p ih =>
      intro u hu
      subst a
      cases b with
      | inl b =>
          simp only [SimpleGraph.sum_adj] at hab
          obtain ⟨v, hv, ⟨q⟩⟩ := ih b rfl
          exact ⟨v, hv, ⟨.cons hab q⟩⟩
      | inr b => simp only [SimpleGraph.sum_adj] at hab

theorem walk_sum_inr_aux
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {a z : V ⊕ W} (p : (G.sum H).Walk a z) :
    ∀ u : W, a = Sum.inr u →
      ∃ v : W, z = Sum.inr v ∧ Nonempty (H.Walk u v) := by
  induction p with
  | nil =>
      intro u hu
      exact ⟨u, hu, ⟨.nil⟩⟩
  | @cons a b z hab p ih =>
      intro u hu
      subst a
      cases b with
      | inl b => simp only [SimpleGraph.sum_adj] at hab
      | inr b =>
          simp only [SimpleGraph.sum_adj] at hab
          obtain ⟨v, hv, ⟨q⟩⟩ := ih b rfl
          exact ⟨v, hv, ⟨.cons hab q⟩⟩

theorem simpleGraph_sum_reachable_inl_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u v : V} :
    (G.sum H).Reachable (Sum.inl u) (Sum.inl v) ↔ G.Reachable u v := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨w, hw, h⟩ := walk_sum_inl_aux p u rfl
    simp only [Sum.inl.injEq] at hw
    subst w
    exact h
  · intro h
    exact h.map SimpleGraph.Embedding.sumInl.toHom

theorem simpleGraph_sum_reachable_inr_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u v : W} :
    (G.sum H).Reachable (Sum.inr u) (Sum.inr v) ↔ H.Reachable u v := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨w, hw, h⟩ := walk_sum_inr_aux p u rfl
    simp only [Sum.inr.injEq] at hw
    subst w
    exact h
  · intro h
    exact h.map SimpleGraph.Embedding.sumInr.toHom

theorem simpleGraph_sum_not_reachable_inl_inr
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u : V} {v : W} :
    ¬(G.sum H).Reachable (Sum.inl u) (Sum.inr v) := by
  rintro ⟨p⟩
  obtain ⟨w, hw, _⟩ := walk_sum_inl_aux p u rfl
  cases hw

theorem simpleGraph_sum_not_reachable_inr_inl
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u : W} {v : V} :
    ¬(G.sum H).Reachable (Sum.inr u) (Sum.inl v) := by
  rintro ⟨p⟩
  obtain ⟨w, hw, _⟩ := walk_sum_inr_aux p u rfl
  cases hw


end
end StatMech.FrontierD
