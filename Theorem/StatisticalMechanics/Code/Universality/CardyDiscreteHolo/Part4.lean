/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part4


namespace StatMech.Universality

open Complex


theorem triContour_expand (F : ℂ → ℂ) (z : Fin 3 → ℂ) :
    triContour F z =
      F ((z 0 + z 1) / 2) * (z 1 - z 0)
      + F ((z 1 + z 2) / 2) * (z 2 - z 1)
      + F ((z 2 + z 0) / 2) * (z 0 - z 2) := by
  unfold triContour
  rw [Fin.sum_univ_three]
  rw [show ((0 : Fin 3) + 1) = 1 from rfl, show ((1 : Fin 3) + 1) = 2 from rfl,
      show ((2 : Fin 3) + 1) = 0 from rfl]


end StatMech.Universality
