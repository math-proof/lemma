/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part3
open scoped BigOperators


namespace StatMech.FrontierA

abbrev QuantumIsingSpaceTimeBlockConfig (n k L : Nat) :=
  Fin n -> QuantumIsingBlockConfig k L

end StatMech.FrontierA
