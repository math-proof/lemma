/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Walls.rc22doublecover.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc22_interCountResidue_iff_famCylBoxResidue :
    rc22_InterCountResidue ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    rw [rc22_reflInter_eq_inter_complFam]; exact h n 𝒜 ℬ
  · intro h n 𝒜 ℬ
    rw [← rc22_reflInter_eq_inter_complFam]; exact h n 𝒜 ℬ


theorem rc22_cylBoxReflInter_of_interCountResidue (h : rc22_InterCountResidue) :
    rc18_CylBoxReflInter :=
  rc20_famCylBoxResidue_iff_cylBoxReflInter.mp
    (rc22_interCountResidue_iff_famCylBoxResidue.mp h)


variable {β : Type*} [DecidableEq β]


theorem rc22_fiber_inter_ineq (am an cm cn : Finset β) :
    #((am ∩ an) ∩ (cm ∪ cn)) + #((am ∪ an) ∩ (cm ∩ cn))
      ≤ #(am ∩ cm) + #(an ∩ cn) := by
  set A := (am ∩ an) ∩ (cm ∪ cn) with hA
  set B := (am ∪ an) ∩ (cm ∩ cn) with hB
  set X := am ∩ cm with hX
  set Y := an ∩ cn with hY
  have hunion : A ∪ B ⊆ X ∪ Y := by
    intro x hx
    simp only [hA, hB, hX, hY, Finset.mem_union, Finset.mem_inter] at hx ⊢
    rcases hx with ⟨⟨hp, hq⟩, hrs⟩ | ⟨hpq, hr, hs⟩
    · rcases hrs with hr | hs
      · exact Or.inl ⟨hp, hr⟩
      · exact Or.inr ⟨hq, hs⟩
    · rcases hpq with hp | hq
      · exact Or.inl ⟨hp, hr⟩
      · exact Or.inr ⟨hq, hs⟩
  have hinter : A ∩ B ⊆ X ∩ Y := by
    intro x hx
    simp only [hA, hB, hX, hY, Finset.mem_inter, Finset.mem_union] at hx ⊢
    obtain ⟨⟨⟨hp, hq⟩, _⟩, _, hr, hs⟩ := hx
    exact ⟨⟨hp, hr⟩, hq, hs⟩
  calc #A + #B
      = #(A ∪ B) + #(A ∩ B) := (Finset.card_union_add_card_inter A B).symm
    _ ≤ #(X ∪ Y) + #(X ∩ Y) :=
        Nat.add_le_add (Finset.card_le_card hunion) (Finset.card_le_card hinter)
    _ = #X + #Y := Finset.card_union_add_card_inter X Y


end StatMech.Walls
