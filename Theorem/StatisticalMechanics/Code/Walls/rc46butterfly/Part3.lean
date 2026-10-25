/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc45doubledcover.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc46butterfly.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc46_dblEmpty02_not_complementary :
    ¬ rc46_isComplementary (dbl (∅ : Finset (Fin 3)) {0, 2}) := by decide


theorem rc46_dblEmpty02_mem_doubleCompress_complBoxDoubled :
    dbl (∅ : Finset (Fin 3)) {0, 2} ∈ doubleCompress 1 (rc37_complBoxDoubled rc46_Acf rc46_Bcf) := by
  rw [rc46_Acf, rc46_Bcf]; decide


theorem rc46_doubleCompress_breaks_complementary_fin3 :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 3))) (i : Fin 3) (U : Finset (Fin 3 ⊕ Fin 3)),
      U ∈ doubleCompress i (rc37_complBoxDoubled 𝒜 ℬ) ∧ ¬ rc46_isComplementary U :=
  ⟨rc46_Acf, rc46_Bcf, 1, dbl (∅ : Finset (Fin 3)) {0, 2},
    rc46_dblEmpty02_mem_doubleCompress_complBoxDoubled, rc46_dblEmpty02_not_complementary⟩


open Classical in


theorem rc46_famCylBoxDoubled_le_at_increasing {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (rc46_famCylBoxDoubled (eventFamily A) (eventFamily B)).card
      ≤ (rc37_complBoxDoubled (eventFamily A) (eventFamily B)).card := by
  rw [rc46_famCylBoxDoubled_card_eq, rc37_complBoxDoubled_card_eq_reflInter]
  exact rc20_famCylBox_of_increasing hA hB


open Classical in


theorem rc46_reimer_closes_of_boxMonoResidue (h : rc44_BoxMonoResidue) :
    rc18_CylBoxReflInter :=
  rc44_reimer_closes_of_boxMonoResidue h

open Classical in


theorem rc46_boxMonoResidue_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) :=
  rc44_boxMonoResidue_fin2 𝒜 ℬ

end StatMech.Walls
