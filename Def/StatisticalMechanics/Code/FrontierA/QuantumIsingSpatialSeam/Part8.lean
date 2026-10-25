/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part7
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingTrotterThermodynamicFreeEnergy
    (beta h : Real) (n : Nat) : Real :=
  if hp : n ≠ 0 ∧ 0 < beta ∧ 0 < beta * h then
    (quantumIsingOpenTrotterAction_almostAdditive
      beta h n hp.1 hp.2.1 hp.2.2).limit
  else 0

end StatMech.FrontierA
