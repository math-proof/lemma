/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
open scoped BigOperators


namespace StatMech.FrontierA

abbrev QuantumIsingBlockConfig (k L : Nat) :=
  Fin k -> QuantumIsingChainConfig L

end StatMech.FrontierA
