/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
@[expose] public section

open scoped BigOperators


namespace StatMech.FrontierA

abbrev QuantumIsingChainConfig (L : Nat) := Fin L -> Bool


end StatMech.FrontierA
