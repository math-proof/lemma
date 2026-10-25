/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectReflectedRowStep_even (x y : Nat) :
    Even (fkRectReflectedRowStep x y) :=
  even_two_mul _

theorem fkRectReflectedRowStep_cast (x y : Nat) :
    (fkRectReflectedRowStep x y : Int) =
      2 * |(y : Int) - x| := by
  rw [fkRectReflectedRowStep, Nat.cast_mul, Nat.cast_ofNat,
    Int.natCast_natAbs]

theorem fkRectReflectedRowStep_of_le {x y : Nat} (hxy : x ≤ y) :
    fkRectReflectedRowStep x y = 2 * (y - x) := by
  unfold fkRectReflectedRowStep
  congr 1
  apply Int.ofNat_injective
  have hnat : (((y : Int) - x).natAbs : Int) = (y - x : Nat) := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    push_cast
    omega
  exact hnat

theorem fkRectReflectedRowStep_of_ge {x y : Nat} (hyx : y ≤ x) :
    fkRectReflectedRowStep x y = 2 * (x - y) := by
  unfold fkRectReflectedRowStep
  congr 1
  apply Int.ofNat_injective
  have hnat : (((y : Int) - x).natAbs : Int) = (x - y : Nat) := by
    rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]
    push_cast
    omega
  exact hnat

theorem fkRectReflectedRowStep_pos_of_span
    (n x y : Nat)
    (hspan : (n : Int) ≤ 2 * |(y : Int) - x| + 2) :
    0 < fkRectReflectedRowStep x y ∨ n ≤ 2 := by
  rw [← fkRectReflectedRowStep_cast] at hspan
  omega

theorem fkRectRowTranslate_eq_add_of_lt
    (R : FKRectTorus) (offset : Nat) (y : Fin R.height)
    (hlt : y.val + offset < R.height) :
    fkRectRowTranslate R offset y = ⟨y.val + offset, hlt⟩ := by
  apply Fin.ext
  rw [fkRectRowTranslate_nat_val, Nat.mod_eq_of_lt hlt]

theorem fkRectRowTranslate_reflection_eq_sub
    (R : FKRectTorus) (offset center : Nat) (y : Fin R.height)
    (hle : y.val ≤ offset + 2 * center)
    (hlt : offset + 2 * center - y.val < R.height) :
    fkRectRowTranslate R offset (fkRectRowReflection R center y) =
      ⟨offset + 2 * center - y.val, hlt⟩ := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    rw [show ((fkRectRowTranslate R offset
        (fkRectRowReflection R center y)).val : ZMod R.height) =
          ((fkRectRowReflection R center y).val : Int) + offset by
      simpa [fkRectRowTranslate] using
        fkRectIntModFin_cast R.height_pos
          (((fkRectRowReflection R center y).val : Int) + offset)]
    push_cast
    rw [fkRectRowReflection_cast, Nat.cast_sub hle]
    push_cast
    ring
  · exact (fkRectRowTranslate R offset
      (fkRectRowReflection R center y)).isLt
  · exact hlt


theorem fkRectEvenRowTranslation_reflection_of_row_le
    (R : FKRectTorus) (x y : R.Vertex) (hxy : x.2.val ≤ y.2.val) :
    fkRectEvenRowTranslationVertexEquiv R
        (fkRectReflectedRowStep x.2.val y.2.val) x =
      fkRectDevelopedReflectionVertexEquiv R y.2.val x := by
  apply Prod.ext
  · rfl
  · change fkRectRowTranslate R
        (fkRectReflectedRowStep x.2.val y.2.val) x.2 =
      fkRectRowReflection R y.2.val x.2
    apply Fin.ext
    apply Nat.ModEq.eq_of_lt_of_lt
    · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
      rw [show ((fkRectRowTranslate R
          (fkRectReflectedRowStep x.2.val y.2.val) x.2).val :
            ZMod R.height) =
          (x.2.val : Int) + fkRectReflectedRowStep x.2.val y.2.val by
        simpa [fkRectRowTranslate] using
          fkRectIntModFin_cast R.height_pos
            ((x.2.val : Int) +
              fkRectReflectedRowStep x.2.val y.2.val)]
      rw [fkRectRowReflection_cast,
        fkRectReflectedRowStep_of_le hxy]
      push_cast
      rw [Nat.cast_sub hxy]
      push_cast
      ring
    · exact (fkRectEvenRowTranslationVertexEquiv R
        (fkRectReflectedRowStep x.2.val y.2.val) x).2.isLt
    · exact (fkRectDevelopedReflectionVertexEquiv R y.2.val x).2.isLt


theorem fkRectEvenRowTranslation_reflection_of_row_ge
    (R : FKRectTorus) (x y : R.Vertex) (hyx : y.2.val ≤ x.2.val) :
    fkRectEvenRowTranslationVertexEquiv R
        (fkRectReflectedRowStep x.2.val y.2.val)
        (fkRectDevelopedReflectionVertexEquiv R y.2.val x) = x := by
  apply Prod.ext
  · rfl
  · change fkRectRowTranslate R
        (fkRectReflectedRowStep x.2.val y.2.val)
          (fkRectRowReflection R y.2.val x.2) = x.2
    apply Fin.ext
    apply Nat.ModEq.eq_of_lt_of_lt
    · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
      rw [show ((fkRectRowTranslate R
          (fkRectReflectedRowStep x.2.val y.2.val)
            (fkRectRowReflection R y.2.val x.2)).val :
            ZMod R.height) =
          ((fkRectRowReflection R y.2.val x.2).val : Int) +
            fkRectReflectedRowStep x.2.val y.2.val by
        simpa [fkRectRowTranslate] using
          fkRectIntModFin_cast R.height_pos
            (((fkRectRowReflection R y.2.val x.2).val : Int) +
                fkRectReflectedRowStep x.2.val y.2.val)]
      push_cast
      rw [fkRectRowReflection_cast,
        fkRectReflectedRowStep_of_ge hyx]
      push_cast
      rw [Nat.cast_sub hyx]
      push_cast
      ring
    · exact (fkRectEvenRowTranslationVertexEquiv R
        (fkRectReflectedRowStep x.2.val y.2.val)
          (fkRectDevelopedReflectionVertexEquiv R y.2.val x)).2.isLt
    · exact x.2.isLt


end
end StatMech.FrontierD
