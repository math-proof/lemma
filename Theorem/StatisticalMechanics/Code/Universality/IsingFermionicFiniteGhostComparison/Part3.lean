/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part3
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFermionicGhostRate_nonneg
    {V : Type*} (boundaryMultiplicity : V → Nat) :
    ∀ x, 0 ≤ isingFermionicGhostRate boundaryMultiplicity x := by
  intro x
  exact mul_nonneg isingFermionicGhostCoefficient_pos.le (by positivity)

theorem isingFermionicGhostRate_pos_iff
    {V : Type*} (boundaryMultiplicity : V → Nat) (x : V) :
    0 < isingFermionicGhostRate boundaryMultiplicity x ↔
      0 < boundaryMultiplicity x := by
  unfold isingFermionicGhostRate
  constructor
  · intro h
    by_contra hx
    have hz : boundaryMultiplicity x = 0 := Nat.eq_zero_of_not_pos hx
    simp [hz] at h
  · intro h
    exact mul_pos isingFermionicGhostCoefficient_pos (by exact_mod_cast h)


theorem isingFermionicGhost_subharmonic_le_ghostValue
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundaryMultiplicity : V → Nat)
    (f : V → Real) (c : Real)
    (hreach : ∀ x, ∃ b, 0 < boundaryMultiplicity b ∧ G.Reachable x b)
    (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x +
      isingFermionicGhostRate boundaryMultiplicity x * (c - f x)) :
    ∀ x, f x ≤ c := by
  apply isingFiniteGhost_subharmonic_le_ghostValue
    G (isingFermionicGhostRate boundaryMultiplicity) f c
    (isingFermionicGhostRate_nonneg boundaryMultiplicity)
  · intro x
    obtain ⟨b, hb, hxb⟩ := hreach x
    exact ⟨b, (isingFermionicGhostRate_pos_iff
      boundaryMultiplicity b).2 hb, hxb⟩
  · exact hmodified


theorem isingFermionicGhost_ghostValue_le_superharmonic
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundaryMultiplicity : V → Nat)
    (f : V → Real) (c : Real)
    (hreach : ∀ x, ∃ b, 0 < boundaryMultiplicity b ∧ G.Reachable x b)
    (hmodified : ∀ x, isingFiniteGraphLaplacian G f x +
      isingFermionicGhostRate boundaryMultiplicity x * (c - f x) ≤ 0) :
    ∀ x, c ≤ f x := by
  apply isingFiniteGhost_ghostValue_le_superharmonic
    G (isingFermionicGhostRate boundaryMultiplicity) f c
    (isingFermionicGhostRate_nonneg boundaryMultiplicity)
  · intro x
    obtain ⟨b, hb, hxb⟩ := hreach x
    exact ⟨b, (isingFermionicGhostRate_pos_iff
      boundaryMultiplicity b).2 hb, hxb⟩
  · exact hmodified


theorem isingFermionicGhost_subharmonic_le_const_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundaryMultiplicity : V → Nat)
    (boundary : V → Prop) (f : V → Real) (ghostValue c : Real)
    (hreach : ∀ x, ∃ b,
      (boundary b ∨ 0 < boundaryMultiplicity b) ∧ G.Reachable x b)
    (hmodified : ∀ x, ¬ boundary x →
      0 ≤ isingFiniteGraphLaplacian G f x +
        isingFermionicGhostRate boundaryMultiplicity x *
          (ghostValue - f x))
    (hghost : ghostValue ≤ c)
    (hboundary : ∀ x, boundary x → f x ≤ c) :
    ∀ x, f x ≤ c := by
  apply isingFiniteGhost_subharmonic_le_const_boundaryWith
    G (isingFermionicGhostRate boundaryMultiplicity) boundary
      f ghostValue c
    (isingFermionicGhostRate_nonneg boundaryMultiplicity)
  · intro x
    obtain ⟨b, hb | hb, hxb⟩ := hreach x
    · exact ⟨b, Or.inl hb, hxb⟩
    · exact ⟨b, Or.inr ((isingFermionicGhostRate_pos_iff
        boundaryMultiplicity b).2 hb), hxb⟩
  · exact hmodified
  · exact hghost
  · exact hboundary


theorem isingFermionicGhost_const_le_superharmonic_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundaryMultiplicity : V → Nat)
    (boundary : V → Prop) (f : V → Real) (ghostValue c : Real)
    (hreach : ∀ x, ∃ b,
      (boundary b ∨ 0 < boundaryMultiplicity b) ∧ G.Reachable x b)
    (hmodified : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G f x +
        isingFermionicGhostRate boundaryMultiplicity x *
          (ghostValue - f x) ≤ 0)
    (hghost : c ≤ ghostValue)
    (hboundary : ∀ x, boundary x → c ≤ f x) :
    ∀ x, c ≤ f x := by
  apply isingFiniteGhost_const_le_superharmonic_boundaryWith
    G (isingFermionicGhostRate boundaryMultiplicity) boundary
      f ghostValue c
    (isingFermionicGhostRate_nonneg boundaryMultiplicity)
  · intro x
    obtain ⟨b, hb | hb, hxb⟩ := hreach x
    · exact ⟨b, Or.inl hb, hxb⟩
    · exact ⟨b, Or.inr ((isingFermionicGhostRate_pos_iff
        boundaryMultiplicity b).2 hb), hxb⟩
  · exact hmodified
  · exact hghost
  · exact hboundary

end
end StatMech.Universality
