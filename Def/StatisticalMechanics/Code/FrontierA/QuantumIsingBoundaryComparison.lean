/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison
open scoped BigOperators


namespace StatMech.FrontierA

def quantumIsingBlockEquiv (k L : Nat) :
    QuantumIsingChainConfig (k * L) ≃ QuantumIsingBlockConfig k L where
  toFun sigma b i := sigma (finProdFinEquiv (b, i))
  invFun sigma j :=
    sigma (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  left_inv sigma := by
    funext j
    change sigma (finProdFinEquiv (finProdFinEquiv.symm j)) = sigma j
    rw [Equiv.apply_symm_apply]
  right_inv sigma := by
    funext b i
    change sigma (finProdFinEquiv.symm (finProdFinEquiv (b, i))).1
      (finProdFinEquiv.symm (finProdFinEquiv (b, i))).2 = sigma b i
    rw [Equiv.symm_apply_apply]

end StatMech.FrontierA
