/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part5
open scoped BigOperators


namespace StatMech.FrontierA

def quantumIsingSpaceTimeBlockSwapEquiv (n k L : Nat) :
    QuantumIsingSpaceTimeBlockConfig n k L ≃
      (Fin k -> Fin n -> QuantumIsingChainConfig L) where
  toFun omega b t := omega t b
  invFun omega t b := omega b t
  left_inv _ := rfl
  right_inv _ := rfl

end StatMech.FrontierA
