/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part3


namespace StatMech.Onsager

open BaseCase

@[simp] theorem onsDiagonalShearDirectionWord_nil :
    onsDiagonalShearDirectionWord [] = [] := rfl

@[simp] theorem onsDiagonalShearDirectionWord_cons
    (d : Fin 4) (tail : List (Fin 4)) :
    onsDiagonalShearDirectionWord (d :: tail) =
      onsDiagonalShearDirectionBlock d ++
        onsDiagonalShearDirectionWord tail := rfl


end StatMech.Onsager
