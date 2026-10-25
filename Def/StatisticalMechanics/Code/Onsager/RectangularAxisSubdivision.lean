/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision


namespace StatMech.Onsager

open BaseCase

def onsAnisotropicStepScale (width height : ℕ) (d : Fin 4) : ℕ :=
  if d = 0 ∨ d = 2 then height else width


def onsAnisotropicDirectionWord (width height : ℕ)
    (word : List (Fin 4)) : List (Fin 4) :=
  word.flatMap fun d ↦ List.replicate (onsAnisotropicStepScale width height d) d

end StatMech.Onsager
