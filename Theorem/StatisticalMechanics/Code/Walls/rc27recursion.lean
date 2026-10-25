/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc26cubefill
import Def.StatisticalMechanics.Code.Walls.rc27recursion
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc27_reflInterRecursion : rc27_ReflInterRecursion (α := α) :=
  fun E 𝒜 ℬ a haE => rc15_card_reflE_slice E 𝒜 ℬ a haE

open Classical in


theorem rc27_reflInter_univ_slice (𝒜 ℬ : Finset (Finset α)) (a : α) :
    #(rc10_reflInter 𝒜 ℬ)
      = #(rc14_reflE (univ.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc14_reflE (univ.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
  rw [← rc15_reflE_univ]
  exact rc15_card_reflE_slice univ 𝒜 ℬ a (Finset.mem_univ a)


set_option maxRecDepth 10000 in


theorem rc27_boxSlice_sum_false :
    ¬ (#(rc14_boxE (univ : Finset (Fin 1)) ({∅}) ({∅}))
        ≤ #(rc14_boxE ((univ : Finset (Fin 1)).erase 0)
              (({∅} : Finset (Finset (Fin 1))).nonMemberSubfamily 0)
              (({∅} : Finset (Finset (Fin 1))).memberSubfamily 0))
          + #(rc14_boxE ((univ : Finset (Fin 1)).erase 0)
              (({∅} : Finset (Finset (Fin 1))).memberSubfamily 0)
              (({∅} : Finset (Finset (Fin 1))).nonMemberSubfamily 0))) := by
  decide

set_option maxRecDepth 10000 in


theorem rc27_boxNesting_false :
    ¬ (rc14_boxE ((univ : Finset (Fin 2)).erase 1)
          (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1)
          (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1)
        ⊆ rc14_boxE ((univ : Finset (Fin 2)).erase 1)
              (({∅} : Finset (Finset (Fin 2))).memberSubfamily 1)
              (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1)
            ∩ rc14_boxE ((univ : Finset (Fin 2)).erase 1)
              (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1)
              (({∅} : Finset (Finset (Fin 2))).memberSubfamily 1)) := by
  decide


end StatMech.Walls
