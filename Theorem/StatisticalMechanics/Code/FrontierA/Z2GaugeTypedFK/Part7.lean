/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part9
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem typedOpenGraph_sup (ends : P -> V × V) (a b : P -> Bool) :
    typedOpenGraph ends (a ⊔ b) =
      typedOpenGraph ends a ⊔ typedOpenGraph ends b := by
  ext x y
  simp only [typedOpenGraph, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨p, hp, hxy, hne⟩
    change (a p || b p) = true at hp
    rw [Bool.or_eq_true] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨p, hp, hxy, hne⟩
    · exact Or.inr ⟨p, hp, hxy, hne⟩
  · rintro (⟨p, hp, hxy, hne⟩ | ⟨p, hp, hxy, hne⟩)
    · refine ⟨p, ?_, hxy, hne⟩
      change (a p || b p) = true
      rw [Bool.or_eq_true]
      exact Or.inl hp
    · refine ⟨p, ?_, hxy, hne⟩
      change (a p || b p) = true
      rw [Bool.or_eq_true]
      exact Or.inr hp

theorem typedOpenGraph_inf_le (ends : P -> V × V) (a b : P -> Bool) :
    typedOpenGraph ends (a ⊓ b) <=
      typedOpenGraph ends a ⊓ typedOpenGraph ends b := by
  intro x y
  simp only [typedOpenGraph, SimpleGraph.inf_adj]
  rintro ⟨p, hp, hxy, hne⟩
  change (a p && b p) = true at hp
  rw [Bool.and_eq_true] at hp
  obtain ⟨ha, hb⟩ := hp
  exact ⟨⟨p, ha, hxy, hne⟩, ⟨p, hb, hxy, hne⟩⟩

theorem typedNumClusters_supermodular (ends : P -> V × V)
    (a b : P -> Bool) :
    typedNumClusters ends a + typedNumClusters ends b <=
      typedNumClusters ends (a ⊔ b) + typedNumClusters ends (a ⊓ b) := by
  have hsub := FK.card_connectedComponent_submodular
    (typedOpenGraph ends a) (typedOpenGraph ends b)
  have hmeet : Nat.card
      (typedOpenGraph ends a ⊓ typedOpenGraph ends b).ConnectedComponent <=
      Nat.card (typedOpenGraph ends (a ⊓ b)).ConnectedComponent :=
    SimpleGraph.ConnectedComponent.card_le_card_of_le
      (typedOpenGraph_inf_le ends a b)
  have h :
      Nat.card (typedOpenGraph ends a).ConnectedComponent +
          Nat.card (typedOpenGraph ends b).ConnectedComponent <=
        Nat.card (typedOpenGraph ends a ⊔
          typedOpenGraph ends b).ConnectedComponent +
          Nat.card (typedOpenGraph ends (a ⊓ b)).ConnectedComponent := by
    omega
  rw [← typedOpenGraph_sup ends a b] at h
  simpa [typedNumClusters] using h

theorem typedSignedCompatible_empty_iff_graphConstant
    (ends : P -> V × V) (omega : P -> Bool) (sigma : V -> Bool) :
    TypedSignedCompatible ends ∅ omega sigma <->
      forall x y, (typedOpenGraph ends omega).Adj x y -> sigma x = sigma y := by
  constructor
  · intro h x y hxy
    obtain ⟨p, hp, hends, hne⟩ := hxy
    have heq : sigma (ends p).1 = sigma (ends p).2 := (h p hp).2 (by simp)
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact heq
    · exact heq.symm
  · intro h p hp
    constructor
    · intro _
      simp
    · intro _
      by_cases hends : (ends p).1 = (ends p).2
      · rw [hends]
      · apply h (ends p).1 (ends p).2
        exact ⟨p, hp, Or.inl ⟨rfl, rfl⟩, hends⟩


end
end StatMech.FrontierA
