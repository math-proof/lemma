/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
import Abbrev.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder
open scoped BigOperators


namespace StatMech.FrontierA

def quantumIsingCyclicSucc {m : Nat} (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

end StatMech.FrontierA
