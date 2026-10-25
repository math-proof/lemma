/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part2


namespace StatMech.Onsager

open BaseCase

theorem onsAnisotropicVertexEmbed_injective
    (width height : ℕ) [NeZero width] [NeZero height] :
    Function.Injective (onsAnisotropicVertexEmbed width height) := by
  have hwidth : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have hheight : 0 < height := Nat.pos_of_ne_zero (NeZero.ne height)
  intro p q hpq
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg (fun z : ZMod (width * height) ×
        ZMod (width * height) ↦ z.1.val) hpq
    simp only [onsAnisotropicVertexEmbed] at hx
    rw [ZMod.val_natCast, ZMod.val_natCast] at hx
    have hpLt : height * p.1.val < width * height := by
      simpa [Nat.mul_comm] using
        (Nat.mul_lt_mul_left hheight).2 p.1.isLt
    have hqLt : height * q.1.val < width * height := by
      simpa [Nat.mul_comm] using
        (Nat.mul_lt_mul_left hheight).2 q.1.isLt
    rw [Nat.mod_eq_of_lt hpLt, Nat.mod_eq_of_lt hqLt] at hx
    exact Nat.eq_of_mul_eq_mul_left hheight hx
  · have hy := congrArg (fun z : ZMod (width * height) ×
        ZMod (width * height) ↦ z.2.val) hpq
    simp only [onsAnisotropicVertexEmbed] at hy
    rw [ZMod.val_natCast, ZMod.val_natCast] at hy
    have hpLt : width * p.2.val < width * height :=
      (Nat.mul_lt_mul_left hwidth).2 p.2.isLt
    have hqLt : width * q.2.val < width * height :=
      (Nat.mul_lt_mul_left hwidth).2 q.2.isLt
    rw [Nat.mod_eq_of_lt hpLt, Nat.mod_eq_of_lt hqLt] at hy
    exact Nat.eq_of_mul_eq_mul_left hwidth hy


theorem onsAnisotropicDirectionWord_preserves_winding
    (width height : ℕ) (word : List (Fin 4)) (mx my : ℤ)
    (hx : (word.map ons_dirExponentX).sum = (width : ℤ) * mx)
    (hy : (word.map ons_dirExponentY).sum = (height : ℤ) * my) :
    ((onsAnisotropicDirectionWord width height word).map
        ons_dirExponentX).sum = (width * height : ℕ) * mx ∧
      ((onsAnisotropicDirectionWord width height word).map
        ons_dirExponentY).sum = (width * height : ℕ) * my := by
  constructor
  · rw [onsAnisotropicDirectionWord_exponentX_sum, hx]
    push_cast
    ring
  · rw [onsAnisotropicDirectionWord_exponentY_sum, hy]
    push_cast
    ring


end StatMech.Onsager
