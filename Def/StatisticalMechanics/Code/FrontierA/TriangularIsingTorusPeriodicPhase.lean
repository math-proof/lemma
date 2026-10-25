/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

def triangularPathDisplacement : List (Fin 6) -> Int × Int
  | [] => 0
  | d :: ds => triangularIntStep d + triangularPathDisplacement ds

def triangularPathVertices : List (Fin 6) -> List (Int × Int)
  | [] => [0]
  | d :: ds =>
      0 :: (triangularPathVertices ds).map (triangularIntStep d + ·)

end StatMech.FrontierA
