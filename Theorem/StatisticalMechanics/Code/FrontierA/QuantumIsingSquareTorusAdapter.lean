module
public import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
public import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


@[simp] theorem squareTorusPositiveDirection_zero :
    squareTorusPositiveDirection 0 = 0 := rfl

@[simp] theorem squareTorusPositiveDirection_one :
    squareTorusPositiveDirection 1 = 1 := rfl

end StatMech.FrontierA
