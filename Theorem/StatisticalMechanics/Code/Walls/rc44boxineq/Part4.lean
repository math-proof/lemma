/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc43reimer.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc44boxineq.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc44_boxMonoResidue_iff_famCylBoxResidue :
    rc44_BoxMonoResidue ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    have := h n 𝒜 ℬ
    rwa [rc44_famCylBoxE_univ, rc44_reflInterE_univ] at this
  · intro h n 𝒜 ℬ
    have := h n 𝒜 ℬ
    rwa [rc44_famCylBoxE_univ, rc44_reflInterE_univ]

open Classical in


theorem rc44_reimer_closes_of_boxMonoResidue (h : rc44_BoxMonoResidue) :
    rc18_CylBoxReflInter :=
  rc20_famCylBoxResidue_iff_cylBoxReflInter.mp (rc44_boxMonoResidue_iff_famCylBoxResidue.mp h)


open Classical in


theorem rc44_boxMonoResidue_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) := by
  rw [rc44_famCylBoxE_univ, rc44_reflInterE_univ]
  exact rc20_famCylBox_fin2 𝒜 ℬ


set_option linter.unusedVariables false in
open Classical in


theorem rc44_reimer_coordinate_induction :
    (rc44_BoxMonoResidue ↔ rc20_FamCylBoxResidue)
      ∧ (rc44_BoxMonoResidue → rc18_CylBoxReflInter)
      ∧ (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)),
          rc44_slab0 a (rc44_famCylBoxE E 𝒜 ℬ)
            ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ))
      ∧ (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)),
          rc44_slab1 a (rc44_famCylBoxE E 𝒜 ℬ)
            ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ))
      ∧ (∀ (E : Finset α) (a : α), a ∈ E → ∀ (𝒜 ℬ : Finset (Finset α)),
          (rc44_reflInterE E 𝒜 ℬ).card
            = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card
              + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card)
      ∧ (({1} : Finset (Fin 3)) ∈ rc44_famCylBoxEComp {0, 1}
            (rc44_slab0 2 rc44_Aref) (rc44_slab0 2 rc44_Bref)
          ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1}
              (rc44_slab0 2 rc44_Aref) (rc44_slab1 2 rc44_Bref)
          ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1}
              (rc44_slab1 2 rc44_Aref) (rc44_slab0 2 rc44_Bref)) :=
  ⟨rc44_boxMonoResidue_iff_famCylBoxResidue,
    rc44_reimer_closes_of_boxMonoResidue,
    fun E a 𝒜 ℬ => rc44_slab0_famCylBoxE_subset E a 𝒜 ℬ,
    fun E a 𝒜 ℬ => rc44_slab1_famCylBoxE_subset E a 𝒜 ℬ,
    fun E a haE 𝒜 ℬ => rc44_reflInterE_card_recursion E a haE 𝒜 ℬ,
    rc44_diagonalSlab_charge_fails_fin3⟩

end StatMech.Walls
