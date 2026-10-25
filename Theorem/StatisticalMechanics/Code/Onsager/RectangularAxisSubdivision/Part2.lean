/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision


namespace StatMech.Onsager

open BaseCase

@[simp] theorem onsAnisotropicDirectionWord_nil (width height : ℕ) :
    onsAnisotropicDirectionWord width height [] = [] := rfl

@[simp] theorem onsAnisotropicDirectionWord_cons
    (width height : ℕ) (d : Fin 4) (tail : List (Fin 4)) :
    onsAnisotropicDirectionWord width height (d :: tail) =
      List.replicate (onsAnisotropicStepScale width height d) d ++
        onsAnisotropicDirectionWord width height tail := rfl

@[simp] theorem onsAnisotropicStepScale_zero (width height : ℕ) :
    onsAnisotropicStepScale width height 0 = height := by
  simp [onsAnisotropicStepScale]

@[simp] theorem onsAnisotropicStepScale_one (width height : ℕ) :
    onsAnisotropicStepScale width height 1 = width := by
  simp [onsAnisotropicStepScale, show (1 : Fin 4) ≠ 0 by decide,
    show (1 : Fin 4) ≠ 2 by decide]

@[simp] theorem onsAnisotropicStepScale_two (width height : ℕ) :
    onsAnisotropicStepScale width height 2 = height := by
  simp [onsAnisotropicStepScale]

@[simp] theorem onsAnisotropicStepScale_three (width height : ℕ) :
    onsAnisotropicStepScale width height 3 = width := by
  simp [onsAnisotropicStepScale, show (3 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 2 by decide]

theorem onsAnisotropicDirectionWord_step_sum
    (width height : ℕ) (word : List (Fin 4)) :
    ((onsAnisotropicDirectionWord width height word).map stepOf).sum =
      ((height : ℤ) * ((word.map stepOf).sum).1,
        (width : ℤ) * ((word.map stepOf).sum).2) := by
  induction word with
  | nil => simp [Prod.ext_iff]
  | cons d tail ih =>
      simp only [onsAnisotropicDirectionWord_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate,
        List.map_cons, List.sum_cons, ih]
      fin_cases d <;>
        simp [stepOf, onsAnisotropicStepScale, Prod.ext_iff] <;> ring

theorem onsAnisotropicDirectionWord_exponentX_sum
    (width height : ℕ) (word : List (Fin 4)) :
    ((onsAnisotropicDirectionWord width height word).map
        ons_dirExponentX).sum =
      (height : ℤ) * (word.map ons_dirExponentX).sum := by
  induction word with
  | nil => simp
  | cons d tail ih =>
      rw [onsAnisotropicDirectionWord_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate, ih]
      fin_cases d <;>
        simp [onsAnisotropicStepScale, ons_dirExponentX] <;> ring

theorem onsAnisotropicDirectionWord_exponentY_sum
    (width height : ℕ) (word : List (Fin 4)) :
    ((onsAnisotropicDirectionWord width height word).map
        ons_dirExponentY).sum =
      (width : ℤ) * (word.map ons_dirExponentY).sum := by
  induction word with
  | nil => simp
  | cons d tail ih =>
      rw [onsAnisotropicDirectionWord_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate, ih]
      fin_cases d <;>
        simp [onsAnisotropicStepScale, ons_dirExponentY] <;> ring


end StatMech.Onsager
