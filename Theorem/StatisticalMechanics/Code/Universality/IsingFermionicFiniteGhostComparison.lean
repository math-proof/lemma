/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteGhostConductance_nonneg
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real)
    (hrate : ∀ x, 0 ≤ ghostRate x) :
    ∀ x y, 0 ≤ isingFiniteGhostConductance G ghostRate x y := by
  classical
  intro x y
  cases x with
  | none =>
      cases y with
      | none => simp [isingFiniteGhostConductance]
      | some y => simpa [isingFiniteGhostConductance] using hrate y
  | some x =>
      cases y with
      | none => simpa [isingFiniteGhostConductance] using hrate x
      | some y =>
          by_cases hxy : G.Adj x y <;>
            simp [isingFiniteGhostConductance, hxy]

theorem isingFiniteGhostConductance_pos_of_adj
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real) :
    ∀ ⦃x y⦄, (isingFiniteGhostGraph G ghostRate).Adj x y →
      0 < isingFiniteGhostConductance G ghostRate x y := by
  classical
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => exact False.elim hxy
      | some y => simpa [isingFiniteGhostConductance] using hxy
  | some x =>
      cases y with
      | none => simpa [isingFiniteGhostConductance] using hxy
      | some y =>
          change G.Adj x y at hxy
          simp [isingFiniteGhostConductance, hxy]


theorem isingFiniteGhostGraph_reachable_boundary
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real)
    (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b) :
    ∀ x : Option V, ∃ b, isingFiniteGhostBoundary b ∧
      (isingFiniteGhostGraph G ghostRate).Reachable x b := by
  intro x
  cases x with
  | none =>
      exact ⟨none, trivial, SimpleGraph.Reachable.refl none⟩
  | some x =>
      obtain ⟨b, hb, hxb⟩ := hreach x
      refine ⟨none, trivial, ?_⟩
      have hsome : (isingFiniteGhostGraph G ghostRate).Reachable (some x) (some b) :=
        hxb.map (isingFiniteGhostInclusion G ghostRate)
      have hghost : (isingFiniteGhostGraph G ghostRate).Reachable (some b) none :=
        (show (isingFiniteGhostGraph G ghostRate).Adj (some b) none from hb).reachable
      exact hsome.trans hghost


theorem isingFiniteGhostGraph_reachable_boundaryWith
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real)
    (boundary : V → Prop)
    (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧
      G.Reachable x b) :
    ∀ x : Option V, ∃ b, isingFiniteGhostBoundaryWith boundary b ∧
      (isingFiniteGhostGraph G ghostRate).Reachable x b := by
  intro x
  cases x with
  | none =>
      exact ⟨none, trivial, SimpleGraph.Reachable.refl none⟩
  | some x =>
      obtain ⟨b, hb | hb, hxb⟩ := hreach x
      · exact ⟨some b, hb,
          hxb.map (isingFiniteGhostInclusion G ghostRate)⟩
      · refine ⟨none, trivial, ?_⟩
        have hsome :
            (isingFiniteGhostGraph G ghostRate).Reachable (some x) (some b) :=
          hxb.map (isingFiniteGhostInclusion G ghostRate)
        have hghost :
            (isingFiniteGhostGraph G ghostRate).Reachable (some b) none :=
          (show (isingFiniteGhostGraph G ghostRate).Adj (some b) none from hb).reachable
        exact hsome.trans hghost


theorem isingFiniteGhostLaplacian_some
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (ghostValue : Real) (f : V → Real) (x : V) :
    isingFiniteWeightedLaplacian
        (isingFiniteGhostConductance G ghostRate)
        (isingFiniteGhostExtension ghostValue f) (some x) =
      isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x) := by
  classical
  unfold isingFiniteWeightedLaplacian isingFiniteGraphLaplacian
  rw [Fintype.sum_option]
  simp only [isingFiniteGhostConductance, isingFiniteGhostExtension]
  rw [add_comm]
  congr 1
  rw [neighborFinset_eq_filter, sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : G.Adj x y <;>
    simp [isingFiniteGhostConductance, hxy]


theorem isingFiniteGhostExtension_subharmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (ghostValue : Real) (f : V → Real)
    (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x +
      ghostRate x * (ghostValue - f x)) :
    IsingFiniteWeightedSubharmonicOn
      (isingFiniteGhostConductance G ghostRate)
      isingFiniteGhostBoundary
      (isingFiniteGhostExtension ghostValue f) := by
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      rw [isingFiniteGhostLaplacian_some]
      exact hmodified x


theorem isingFiniteGhostExtension_superharmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (ghostValue : Real) (f : V → Real)
    (hmodified : ∀ x, isingFiniteGraphLaplacian G f x +
      ghostRate x * (ghostValue - f x) ≤ 0) :
    IsingFiniteWeightedSuperharmonicOn
      (isingFiniteGhostConductance G ghostRate)
      isingFiniteGhostBoundary
      (isingFiniteGhostExtension ghostValue f) := by
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      rw [isingFiniteGhostLaplacian_some]
      exact hmodified x


theorem isingFiniteGhostExtension_subharmonicOn_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (boundary : V → Prop) (ghostValue : Real) (f : V → Real)
    (hmodified : ∀ x, ¬ boundary x →
      0 ≤ isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x)) :
    IsingFiniteWeightedSubharmonicOn
      (isingFiniteGhostConductance G ghostRate)
      (isingFiniteGhostBoundaryWith boundary)
      (isingFiniteGhostExtension ghostValue f) := by
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      rw [isingFiniteGhostLaplacian_some]
      exact hmodified x hx


theorem isingFiniteGhostExtension_superharmonicOn_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (boundary : V → Prop) (ghostValue : Real) (f : V → Real)
    (hmodified : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x) ≤ 0) :
    IsingFiniteWeightedSuperharmonicOn
      (isingFiniteGhostConductance G ghostRate)
      (isingFiniteGhostBoundaryWith boundary)
      (isingFiniteGhostExtension ghostValue f) := by
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      rw [isingFiniteGhostLaplacian_some]
      exact hmodified x hx


theorem isingFiniteGhost_subharmonic_le_ghostValue
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (f : V → Real) (c : Real)
    (hrate : ∀ x, 0 ≤ ghostRate x)
    (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b)
    (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x +
      ghostRate x * (c - f x)) :
    ∀ x, f x ≤ c := by
  intro x
  have h := isingFiniteWeighted_subharmonic_le_const
    (isingFiniteGhostGraph G ghostRate)
    (isingFiniteGhostConductance G ghostRate)
    isingFiniteGhostBoundary (isingFiniteGhostExtension c f) c
    (isingFiniteGhostConductance_nonneg G ghostRate hrate)
    (isingFiniteGhostConductance_pos_of_adj G ghostRate)
    (isingFiniteGhostGraph_reachable_boundary G ghostRate hreach)
    (isingFiniteGhostExtension_subharmonicOn
      G ghostRate c f hmodified)
    (by
      intro y hy
      cases y with
      | none => rfl
      | some y => simp [isingFiniteGhostBoundary] at hy)
  exact h (some x)


theorem isingFiniteGhost_ghostValue_le_superharmonic
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (f : V → Real) (c : Real)
    (hrate : ∀ x, 0 ≤ ghostRate x)
    (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b)
    (hmodified : ∀ x, isingFiniteGraphLaplacian G f x +
      ghostRate x * (c - f x) ≤ 0) :
    ∀ x, c ≤ f x := by
  intro x
  have h := isingFiniteWeighted_const_le_superharmonic
    (isingFiniteGhostGraph G ghostRate)
    (isingFiniteGhostConductance G ghostRate)
    isingFiniteGhostBoundary (isingFiniteGhostExtension c f) c
    (isingFiniteGhostConductance_nonneg G ghostRate hrate)
    (isingFiniteGhostConductance_pos_of_adj G ghostRate)
    (isingFiniteGhostGraph_reachable_boundary G ghostRate hreach)
    (isingFiniteGhostExtension_superharmonicOn
      G ghostRate c f hmodified)
    (by
      intro y hy
      cases y with
      | none => rfl
      | some y => simp [isingFiniteGhostBoundary] at hy)
  exact h (some x)


theorem isingFiniteGhost_subharmonic_le_const_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real) (boundary : V → Prop)
    (f : V → Real) (ghostValue c : Real)
    (hrate : ∀ x, 0 ≤ ghostRate x)
    (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧
      G.Reachable x b)
    (hmodified : ∀ x, ¬ boundary x →
      0 ≤ isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x))
    (hghost : ghostValue ≤ c)
    (hboundary : ∀ x, boundary x → f x ≤ c) :
    ∀ x, f x ≤ c := by
  intro x
  have h := isingFiniteWeighted_subharmonic_le_const
    (isingFiniteGhostGraph G ghostRate)
    (isingFiniteGhostConductance G ghostRate)
    (isingFiniteGhostBoundaryWith boundary)
    (isingFiniteGhostExtension ghostValue f) c
    (isingFiniteGhostConductance_nonneg G ghostRate hrate)
    (isingFiniteGhostConductance_pos_of_adj G ghostRate)
    (isingFiniteGhostGraph_reachable_boundaryWith
      G ghostRate boundary hreach)
    (isingFiniteGhostExtension_subharmonicOn_boundaryWith
      G ghostRate boundary ghostValue f hmodified)
    (by
      intro y hy
      cases y with
      | none => exact hghost
      | some y => exact hboundary y hy)
  exact h (some x)


theorem isingFiniteGhost_const_le_superharmonic_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real) (boundary : V → Prop)
    (f : V → Real) (ghostValue c : Real)
    (hrate : ∀ x, 0 ≤ ghostRate x)
    (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧
      G.Reachable x b)
    (hmodified : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x) ≤ 0)
    (hghost : c ≤ ghostValue)
    (hboundary : ∀ x, boundary x → c ≤ f x) :
    ∀ x, c ≤ f x := by
  intro x
  have h := isingFiniteWeighted_const_le_superharmonic
    (isingFiniteGhostGraph G ghostRate)
    (isingFiniteGhostConductance G ghostRate)
    (isingFiniteGhostBoundaryWith boundary)
    (isingFiniteGhostExtension ghostValue f) c
    (isingFiniteGhostConductance_nonneg G ghostRate hrate)
    (isingFiniteGhostConductance_pos_of_adj G ghostRate)
    (isingFiniteGhostGraph_reachable_boundaryWith
      G ghostRate boundary hreach)
    (isingFiniteGhostExtension_superharmonicOn_boundaryWith
      G ghostRate boundary ghostValue f hmodified)
    (by
      intro y hy
      cases y with
      | none => exact hghost
      | some y => exact hboundary y hy)
  exact h (some x)


end
end StatMech.Universality
