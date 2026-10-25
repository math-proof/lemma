/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc57witnessed
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc57_naturalSDR_closes_residue (h : rc57_NaturalSDR) : rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  obtain ⟨f, hinj, hmem⟩ := h n 𝒜 ℬ
  refine Finset.card_le_card_of_injOn f (fun S hS => ?_) hinj
  exact rc21_admComp_subset_reflInter n 𝒜 ℬ S (hmem S hS)

open Classical in


theorem rc57_reimer_closes_of_naturalSDR (h : rc57_NaturalSDR) : rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue (rc57_naturalSDR_closes_residue h)

open Classical in


theorem rc57_hall_iff_sdr (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∀ 𝒮 : Finset (rc20_famCylBox 𝒜 ℬ),
        #𝒮 ≤ #(𝒮.biUnion (fun S => rc21_admComp n 𝒜 ℬ (S : Finset (Fin n))))) ↔
      ∃ f : (rc20_famCylBox 𝒜 ℬ) → Finset (Fin n),
        Function.Injective f ∧
          ∀ S : (rc20_famCylBox 𝒜 ℬ), f S ∈ rc21_admComp n 𝒜 ℬ (S : Finset (Fin n)) :=
  Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun S : (rc20_famCylBox 𝒜 ℬ) =>
      rc21_admComp n 𝒜 ℬ (S : Finset (Fin n)))


end StatMech.Walls
