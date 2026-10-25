/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


def squareTorusPositiveDirection (mu : Fin 2) : Fin 4 :=
  ⟨mu.val, lt_trans mu.isLt (by omega)⟩

end StatMech.FrontierA
