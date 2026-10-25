/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part5


namespace StatMech.Universality

open Complex


theorem triContour_eq_cardyS (F : ℂ → ℂ) (v d : ℂ) :
    triContour F (triFace v d)
      = (cardyOmega - 1) * d * ( F ((triFace v d 0 + triFace v d 1) / 2)
          + cardyOmega * F ((triFace v d 1 + triFace v d 2) / 2)
          + cardyOmega ^ 2 * F ((triFace v d 2 + triFace v d 0) / 2) ) := by
  rw [triContour_expand]
  have e1 : triFace v d 1 - triFace v d 0 = (cardyOmega - 1) * d := by
    show (v + cardyOmega * d) - (v + d) = (cardyOmega - 1) * d; ring
  have e2 : triFace v d 2 - triFace v d 1 = cardyOmega * (cardyOmega - 1) * d := by
    show (v + cardyOmega ^ 2 * d) - (v + cardyOmega * d) = cardyOmega * (cardyOmega - 1) * d; ring
  have e3 : triFace v d 0 - triFace v d 2 = cardyOmega ^ 2 * (cardyOmega - 1) * d := by
    show (v + d) - (v + cardyOmega ^ 2 * d) = cardyOmega ^ 2 * (cardyOmega - 1) * d
    rw [show cardyOmega ^ 2 * (cardyOmega - 1) * d = (cardyOmega ^ 3 - cardyOmega ^ 2) * d by ring,
        cardyOmega_cube]; ring
  rw [e1, e2, e3]; ring


end StatMech.Universality
