/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part7


namespace StatMech.Onsager

open BaseCase

theorem onsRectangularShearSubdivisionWord_cyclicNonUturn
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (word : List (Fin 4))
    (hcyclic : onsCyclicDirectionNonUturn word) :
    onsCyclicDirectionNonUturn
      (onsRectangularShearSubdivisionWord width height word) := by
  unfold onsRectangularShearSubdivisionWord
  apply onsAnisotropicDirectionWord_cyclicNonUturn
      (4 * width) (2 * height) (by positivity) (by positivity)
  exact onsDiagonalShearDirectionWord_cyclicNonUturn word hcyclic

theorem onsRectangularShearSubdivisionWord_preserves_deck_winding
    (width height : ℕ) (word : List (Fin 4)) (x y : ℤ)
    (hdisp : (word.map stepOf).sum =
      ((2 * width : ℕ) * x + (height : ℤ) * y,
        (2 * width : ℕ) * x - (height : ℤ) * y)) :
    ((onsRectangularShearSubdivisionWord width height word).map
        ons_dirExponentX).sum = (8 * width * height : ℕ) * x ∧
      ((onsRectangularShearSubdivisionWord width height word).map
        ons_dirExponentY).sum = (8 * width * height : ℕ) * y := by
  have hshear := onsDiagonalShearDirectionWord_step_sum word
  rw [hdisp] at hshear
  have hx : ((onsDiagonalShearDirectionWord word).map
      ons_dirExponentX).sum = (4 * width : ℕ) * x := by
    have h := congrArg Prod.fst hshear
    rw [onsDirectionWord_stepOf_fst_sum] at h
    calc
      _ = ((2 * width : ℕ) : ℤ) * x + (height : ℤ) * y +
          (((2 * width : ℕ) : ℤ) * x - (height : ℤ) * y) := by
        simpa only [Prod.fst, Prod.snd] using h
      _ = (4 * width : ℕ) * x := by push_cast; ring
  have hy : ((onsDiagonalShearDirectionWord word).map
      ons_dirExponentY).sum = (2 * height : ℕ) * y := by
    have h := congrArg Prod.snd hshear
    rw [onsDirectionWord_stepOf_snd_sum] at h
    calc
      _ = ((2 * width : ℕ) : ℤ) * x + (height : ℤ) * y -
          (((2 * width : ℕ) : ℤ) * x - (height : ℤ) * y) := by
        simpa only [Prod.fst, Prod.snd] using h
      _ = (2 * height : ℕ) * y := by push_cast; ring
  have hscaled := onsAnisotropicDirectionWord_preserves_winding
    (4 * width) (2 * height) (onsDiagonalShearDirectionWord word) x y hx hy
  simpa [onsRectangularShearSubdivisionWord, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hscaled

end StatMech.Onsager
