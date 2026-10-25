/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc23boxmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Def.StatisticalMechanics.Code.Walls.rc24countbridge.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc24_upCompComp_eq (n : ℕ) (i : Fin n) (𝒜 : Finset (Finset (Fin n))) :
    rc24_upCompComp n i 𝒜 = rc22_upComp i 𝒜 := by
  rw [rc24_upCompComp, rc24_upComp_eq_complConj]

set_option maxHeartbeats 4000000 in


theorem rc24_boxDownUpMono_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2) :
    #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (Down.compression i 𝒜) (rc22_upComp i ℬ)) := by
  rw [← rc24_upCompComp_eq, ← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  revert 𝒜 ℬ i
  decide


open Classical in


theorem rc24_reflInter_downUp_increases :
    #(rc10_reflInter ({∅} : Finset (Finset (Fin 2))) ({{0}}))
      < #(rc10_reflInter (Down.compression 1 ({∅} : Finset (Finset (Fin 2))))
          (rc22_upComp 1 ({{0}} : Finset (Finset (Fin 2))))) := by
  rw [← rc24_upCompComp_eq, ← rc20_reflInterComp_eq, ← rc20_reflInterComp_eq]
  decide


open Classical in


theorem rc24_famCylBox_violates_fiberRecursion :
    #(rc20_famCylBox ({∅} : Finset (Finset (Fin 2))) (univ))
      ≠ #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0)
            ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0))
        + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).memberSubfamily 0)
            ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0))
        + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0)
            ((univ : Finset (Finset (Fin 2))).memberSubfamily 0)) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq,
    ← rc20_famCylBoxComp_eq]
  decide


open Classical in


theorem rc24_reimer_countbridge :
    (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ = rc24_complCylBox 𝒜 ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
          #(rc20_famCylBox 𝒜 ℬ)
            ≤ #(rc20_famCylBox (Down.compression i 𝒜) (rc22_upComp i ℬ)))
      ∧ (#(rc10_reflInter ({∅} : Finset (Finset (Fin 2))) ({{0}}))
          < #(rc10_reflInter (Down.compression 1 ({∅} : Finset (Finset (Fin 2))))
              (rc22_upComp 1 ({{0}} : Finset (Finset (Fin 2))))))
      ∧ (#(rc20_famCylBox ({∅} : Finset (Finset (Fin 2))) (univ))
          ≠ #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0)
                ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0))
            + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).memberSubfamily 0)
                ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0))
            + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0)
                ((univ : Finset (Finset (Fin 2))).memberSubfamily 0))) :=
  ⟨rc24_famCylBox_eq_complCylBox, rc24_boxDownUpMono_fin2, rc24_reflInter_downUp_increases,
    rc24_famCylBox_violates_fiberRecursion⟩

end StatMech.Walls
