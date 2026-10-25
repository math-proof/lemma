/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
import Def.StatisticalMechanics.Code.Walls.rc81shifttomonotone.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc81_reflInter_orig_zero : (rc80_reflInterG rc81_wA rc81_wA).card = 0 := by decide


theorem rc81_wA_not_upper : ¬ rc80_IsUpper rc81_wA := by
  intro h
  have hbot : rc81_botF ∈ rc81_wA := Finset.mem_singleton_self _
  have := h rc81_botF hbot 0
  rw [rc81_wA, Finset.mem_singleton] at this
  have hne : Function.update rc81_botF 0 true ≠ rc81_botF := by
    intro heq
    have : Function.update rc81_botF 0 true 0 = rc81_botF 0 := by rw [heq]
    simp [Function.update_self, rc81_botF] at this
  exact hne this


theorem rc81_upClosure_wA_univ :
    rc81_upClosure rc81_wA = (Finset.univ : Finset (ConfigSpace (Fin 2))) := by decide


theorem rc81_reflInter_shifted_one :
    (rc80_reflInterG (rc81_upClosure rc81_wA) rc81_wA).card = 1 := by decide


theorem rc81_shift_refutes_wall_witness :
    (rc80_reflInterG rc81_wA rc81_wA).card
      < (rc80_reflInterG (rc81_upClosure rc81_wA) rc81_wA).card := by
  rw [rc81_reflInter_orig_zero, rc81_reflInter_shifted_one]; exact Nat.zero_lt_one


theorem rc81_occ_mono {A A' : Finset (ConfigSpace ι)} (h : A ⊆ A') (K : Finset ι)
    (w : ConfigSpace ι) (hocc : rc80_occ A K w = true) : rc80_occ A' K w = true := by
  unfold rc80_occ at hocc ⊢
  rw [decide_eq_true_eq] at hocc ⊢
  intro w' hw'; exact h (hocc w' hw')


theorem rc81_disjOcc_mono {A A' B B' : Finset (ConfigSpace ι)} (hA : A ⊆ A') (hB : B ⊆ B') :
    rc80_disjOccG A B ⊆ rc80_disjOccG A' B' := by
  intro w hw
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  obtain ⟨K, L, hKL, hK, hL⟩ := hw
  exact ⟨K, L, hKL, rc81_occ_mono hA K w hK, rc81_occ_mono hB L w hL⟩

open Classical in


theorem rc81_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc80_reimerWprobCore_of_boxUnionBound h


theorem rc81_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc80_IsUpper (rc81_upClosure A)) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        rc80_IsLower (rc81_downClosure B)) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        (rc80_reflInterG A B).card ≤ (rc80_reflInterG (rc81_upClosure A) B).card) ∧
    
    ((rc80_reflInterG rc81_wA rc81_wA).card
        < (rc80_reflInterG (rc81_upClosure rc81_wA) rc81_wA).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A A' B B' : Finset (ConfigSpace ι)},
        A ⊆ A' → B ⊆ B' → rc80_disjOccG A B ⊆ rc80_disjOccG A' B') ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun A => rc81_upClosure_isUpper A,
   fun B => rc81_downClosure_isLower B,
   fun A B => rc81_upClosure_reflInter_ge A B,
   rc81_shift_refutes_wall_witness,
   fun hA hB => rc81_disjOcc_mono hA hB,
   rc81_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
