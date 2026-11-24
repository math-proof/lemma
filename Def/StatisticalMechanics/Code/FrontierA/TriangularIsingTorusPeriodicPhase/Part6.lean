module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
public import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part5
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

def triangularSwapDirection : Fin 6 -> Fin 6 := ![2, 3, 0, 1, 4, 5]

def triangularSwapPoint (p : Int × Int) : Int × Int := (p.2, p.1)

end StatMech.FrontierA
