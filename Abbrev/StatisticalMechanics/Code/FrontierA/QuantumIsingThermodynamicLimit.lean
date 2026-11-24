module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
open scoped BigOperators
open Filter


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

abbrev QuantumIsingTwoBlockConfig (A B : Nat) :=
  QuantumIsingChainConfig A × QuantumIsingChainConfig B

end StatMech.FrontierA
