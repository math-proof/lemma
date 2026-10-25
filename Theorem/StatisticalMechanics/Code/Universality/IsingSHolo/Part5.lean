/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.IsingSHolo.Part5


namespace StatMech.Universality

open Complex


theorem isingContour_expand (F : ℂ → ℂ) (z : Fin 4 → ℂ) :
    isingContour F z =
      F ((z 0 + z 1) / 2) * (z 1 - z 0)
      + F ((z 1 + z 2) / 2) * (z 2 - z 1)
      + F ((z 2 + z 3) / 2) * (z 3 - z 2)
      + F ((z 3 + z 0) / 2) * (z 0 - z 3) := by
  unfold isingContour
  rw [Fin.sum_univ_four]
  rw [show ((0 : Fin 4) + 1) = 1 from rfl, show ((1 : Fin 4) + 1) = 2 from rfl,
      show ((2 : Fin 4) + 1) = 3 from rfl, show ((3 : Fin 4) + 1) = 0 from rfl]


end StatMech.Universality
