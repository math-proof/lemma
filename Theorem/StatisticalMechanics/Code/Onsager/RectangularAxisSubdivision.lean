/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity


namespace StatMech.Onsager

open BaseCase

theorem onsDirectionWord_stepOf_fst_sum (word : List (Fin 4)) :
    ((word.map stepOf).sum).1 = (word.map ons_dirExponentX).sum := by
  induction word with
  | nil => rfl
  | cons d tail ih =>
      simp only [List.map_cons, List.sum_cons, Prod.fst_add, ih]
      fin_cases d <;> rfl

theorem onsDirectionWord_stepOf_snd_sum (word : List (Fin 4)) :
    ((word.map stepOf).sum).2 = (word.map ons_dirExponentY).sum := by
  induction word with
  | nil => rfl
  | cons d tail ih =>
      simp only [List.map_cons, List.sum_cons, Prod.snd_add, ih]
      fin_cases d <;> rfl


end StatMech.Onsager
