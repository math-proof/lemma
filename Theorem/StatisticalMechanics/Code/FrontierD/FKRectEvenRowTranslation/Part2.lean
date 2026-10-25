/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Def.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part2
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectRowTranslationEquiv_apply
    (R : FKRectTorus) (s : Int) (y : Fin R.height) :
    fkRectRowTranslationEquiv R s y = fkRectRowTranslate R s y := rfl

theorem fkRectRowTranslate_nat_val
    (R : FKRectTorus) (s : Nat) (y : Fin R.height) :
    (fkRectRowTranslate R s y).val = (y.val + s) % R.height := by
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    rw [show ((fkRectRowTranslate R s y).val : ZMod R.height) =
        (y.val : Int) + s by
      simpa [fkRectRowTranslate] using fkRectIntModFin_cast R.height_pos
        ((y.val : Int) + s)]
    simp
  · exact (fkRectRowTranslate R s y).isLt
  · exact Nat.mod_lt _ R.height_pos

@[simp] theorem fkRectRowTranslate_zero
    (R : FKRectTorus) (y : Fin R.height) :
    fkRectRowTranslate R 0 y = y := by
  change fkRectRowTranslate R (0 : Nat) y = y
  apply Fin.ext
  rw [fkRectRowTranslate_nat_val]
  simp only [Nat.add_zero]
  exact Nat.mod_eq_of_lt y.isLt


theorem fkRectRowTranslate_even_iff
    (R : FKRectTorus) (s : Nat) (hs : Even s) (y : Fin R.height) :
    Even (fkRectRowTranslate R s y).val ↔ Even y.val := by
  rw [fkRectRowTranslate_nat_val,
    Even.mod_even_iff R.height_even, Nat.even_add]
  simp [hs]

theorem fkRectCyclicPred_cast (R : FKRectTorus)
    (y : Fin R.height) :
    ((SixVertexArrows.cyclicPred R.height_pos y).val : ZMod R.height) =
      (y.val : ZMod R.height) - 1 := by
  rw [fkRectCyclicPred_val]
  split <;> rename_i h
  · rw [Nat.cast_sub (by omega : 1 ≤ R.height)]
    push_cast
    simp
    rw [h]
    simp
  · rw [Nat.cast_sub (by omega : 1 ≤ y.val)]
    push_cast
    ring


theorem fkRectRowTranslate_cyclicPred
    (R : FKRectTorus) (s : Int) (y : Fin R.height) :
    fkRectRowTranslate R s
        (SixVertexArrows.cyclicPred R.height_pos y) =
      SixVertexArrows.cyclicPred R.height_pos
        (fkRectRowTranslate R s y) := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    rw [show ((fkRectRowTranslate R s
        (SixVertexArrows.cyclicPred R.height_pos y)).val :
          ZMod R.height) =
        (SixVertexArrows.cyclicPred R.height_pos y).val + s by
      simpa [fkRectRowTranslate] using fkRectIntModFin_cast R.height_pos
        ((SixVertexArrows.cyclicPred R.height_pos y).val + s)]
    rw [fkRectCyclicPred_cast, fkRectCyclicPred_cast]
    rw [show ((fkRectRowTranslate R s y).val : ZMod R.height) =
        (y.val : Int) + s by
      simpa [fkRectRowTranslate] using fkRectIntModFin_cast R.height_pos
        ((y.val : Int) + s)]
    push_cast
    ring
  · exact (fkRectRowTranslate R s
      (SixVertexArrows.cyclicPred R.height_pos y)).isLt
  · exact (SixVertexArrows.cyclicPred R.height_pos
      (fkRectRowTranslate R s y)).isLt


theorem fkRectRowTranslate_add
    (R : FKRectTorus) (a b : Nat) (y : Fin R.height) :
    fkRectRowTranslate R a (fkRectRowTranslate R b y) =
      fkRectRowTranslate R (a + b) y := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    simp only [fkRectRowTranslate]
    rw [fkRectIntModFin_cast]
    push_cast
    rw [fkRectIntModFin_cast, fkRectIntModFin_cast]
    push_cast
    ring
  · exact (fkRectRowTranslate R a (fkRectRowTranslate R b y)).isLt
  · exact (fkRectRowTranslate R (a + b) y).isLt


end
end StatMech.FrontierD
