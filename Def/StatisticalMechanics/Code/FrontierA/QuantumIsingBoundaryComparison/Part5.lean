/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part4
open scoped BigOperators


namespace StatMech.FrontierA

def quantumIsingSpaceTimeBlockEquiv (n k L : Nat) :
    (Fin n -> QuantumIsingChainConfig (k * L)) ≃
      QuantumIsingSpaceTimeBlockConfig n k L :=
  Equiv.piCongrRight (fun _ : Fin n => quantumIsingBlockEquiv k L)

end StatMech.FrontierA
