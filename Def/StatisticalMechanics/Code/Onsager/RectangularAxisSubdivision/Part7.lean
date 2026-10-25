/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part7


namespace StatMech.Onsager

open BaseCase

def onsRectangularShearSubdivisionWord (width height : ℕ)
    (word : List (Fin 4)) : List (Fin 4) :=
  onsAnisotropicDirectionWord (4 * width) (2 * height)
    (onsDiagonalShearDirectionWord word)


end StatMech.Onsager
