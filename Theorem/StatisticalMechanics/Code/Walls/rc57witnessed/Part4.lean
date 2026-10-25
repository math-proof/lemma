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
import Def.StatisticalMechanics.Code.Walls.rc57witnessed.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc57_reflMatching_iff_witnessedInterResidue :
    rc57_ReflMatching ↔ rc56_WitnessedInterResidue := by
  constructor
  · intro h n 𝒜 ℬ
    exact (rc57_witnessedInter_iff_injection 𝒜 ℬ).mpr (h n 𝒜 ℬ)
  · intro h n 𝒜 ℬ
    exact (rc57_witnessedInter_iff_injection 𝒜 ℬ).mp (h n 𝒜 ℬ)

open Classical in


theorem rc57_reimer_closes_of_reflMatching (h : rc57_ReflMatching) : rc18_CylBoxReflInter :=
  rc56_reimer_closes_of_witnessedInterResidue
    (rc57_reflMatching_iff_witnessedInterResidue.mp h)


open Classical in


theorem rc57_reimer_matching :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) ↔
          Nonempty (((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) : Finset (Finset (Fin 3)))
            ↪ (𝒜 ∩ rc22_complFam ℬ : Finset (Finset (Fin 3)))))
      ∧ (rc57_ReflMatching ↔ rc56_WitnessedInterResidue)
      ∧ (rc57_ReflMatching → rc18_CylBoxReflInter)
      ∧ (rc57_NaturalSDR → rc18_CylBoxReflInter)
      ∧ ((rc57_natNbhd 3 rc57_Anat rc57_Bnat).card
          < (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card)
      ∧ ((rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card
          ≤ (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card) :=
  ⟨fun 𝒜 ℬ => rc57_witnessedInter_iff_injection 𝒜 ℬ,
    rc57_reflMatching_iff_witnessedInterResidue,
    rc57_reimer_closes_of_reflMatching,
    rc57_reimer_closes_of_naturalSDR,
    rc57_naturalHall_fails_fin3,
    rc57_wall_holds_on_natRes⟩

end StatMech.Walls
