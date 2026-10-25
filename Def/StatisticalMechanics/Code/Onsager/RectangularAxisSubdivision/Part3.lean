/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part3


namespace StatMech.Onsager

open BaseCase

def onsDiagonalShearDirectionBlock (d : Fin 4) : List (Fin 4) :=
  match d.val with
  | 0 => [0, 1]
  | 1 => [0, 3]
  | 2 => [2, 3]
  | _ => [2, 1]


def onsDiagonalShearDirectionWord (word : List (Fin 4)) : List (Fin 4) :=
  word.flatMap onsDiagonalShearDirectionBlock

end StatMech.Onsager
