/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc44boxineq.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc45doubledcover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc45_reflInterE_slabSwap_fails_fin3 :
    (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card
        + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card
      < (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card
        + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card := by
  rw [rc45_Aswap, rc45_Bswap, rc44_slab0, rc44_slab0, rc44_slab1, rc44_slab1]
  decide


open Classical in


theorem rc45_reimer_closes_of_boxMonoResidue (h : rc44_BoxMonoResidue) :
    rc18_CylBoxReflInter :=
  rc44_reimer_closes_of_boxMonoResidue h

open Classical in


theorem rc45_boxMonoResidue_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) :=
  rc44_boxMonoResidue_fin2 𝒜 ℬ


set_option linter.unusedVariables false in
open Classical in


theorem rc45_reimer_doubledcover :
    (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)),
        (rc44_famCylBoxE E 𝒜 ℬ).card
          ≤ (rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ)).card
            + (rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ)).card)
      ∧ (∀ (E : Finset α) (a : α), a ∈ E → ∀ (𝒜 ℬ : Finset (Finset α)),
          (rc44_reflInterE E 𝒜 ℬ).card
            = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card
              + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card)
      ∧ ((rc44_reflInterEComp (Finset.univ : Finset (Fin 3)) rc45_Astep rc45_Bstep).card
            < (rc44_famCylBoxEComp {0, 1}
                  (rc44_slab0 2 rc45_Astep) (rc44_slab0 2 rc45_Bstep)).card
              + (rc44_famCylBoxEComp {0, 1}
                  (rc44_slab1 2 rc45_Astep) (rc44_slab1 2 rc45_Bstep)).card)
      ∧ ((rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card
            + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card
          < (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card
            + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card)
      ∧ (rc44_BoxMonoResidue → rc18_CylBoxReflInter) :=
  ⟨fun E a 𝒜 ℬ => rc45_famCylBoxE_card_diagonal_ub E a 𝒜 ℬ,
    fun E a haE 𝒜 ℬ => rc45_reflInterE_card_antidiagonal E a haE 𝒜 ℬ,
    rc45_diagonalBox_exceeds_reflInter_fin3,
    rc45_reflInterE_slabSwap_fails_fin3,
    rc45_reimer_closes_of_boxMonoResidue⟩

end StatMech.Walls
