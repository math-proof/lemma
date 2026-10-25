/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part6


namespace StatMech.Onsager

open BaseCase

noncomputable def onsDirectionWordTorusDart
    (L : ℕ) (word : List (Fin 4)) [NeZero word.length] :
    Fin word.length → ons_Dart L := by
  let dir : Fin word.length → Fin 4 := word.get
  exact fun k ↦
    (ons_reduceSite L (BaseCase.pos dir (-k)), dir (-k))

end StatMech.Onsager
