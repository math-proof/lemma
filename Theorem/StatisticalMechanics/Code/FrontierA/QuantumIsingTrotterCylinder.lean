/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder
open scoped BigOperators


namespace StatMech.FrontierA

@[simp] theorem quantumIsingCyclicSucc_eq_add_one {m : Nat} [NeZero m]
    (i : Fin m) : quantumIsingCyclicSucc i = i + 1 := by
  apply Fin.ext
  simp [quantumIsingCyclicSucc, Fin.val_add]


end StatMech.FrontierA
