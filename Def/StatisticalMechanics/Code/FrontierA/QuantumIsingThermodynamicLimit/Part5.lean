/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part4
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

def quantumIsingSpaceTimeTwoBlockSplitEquiv (n A B : Nat) :
    QuantumIsingSpaceTimeTwoBlockConfig n A B ≃
      (Fin n -> QuantumIsingChainConfig A) ×
        (Fin n -> QuantumIsingChainConfig B) where
  toFun omega := (fun t => (omega t).1, fun t => (omega t).2)
  invFun pair t := (pair.1 t, pair.2 t)
  left_inv _ := rfl
  right_inv _ := rfl

end StatMech.FrontierA
