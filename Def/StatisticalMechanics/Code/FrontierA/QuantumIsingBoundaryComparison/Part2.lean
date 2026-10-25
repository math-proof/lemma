/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingBlockOpenInteraction (k L : Nat)
    (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) : Real :=
  ∑ b : Fin (k + 1), ∑ i : Fin L,
    quantumIsingSpinSign (sigma b i.castSucc) *
      quantumIsingSpinSign (sigma b i.succ)

noncomputable def quantumIsingBlockPeriodicInteraction (k L : Nat)
    (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) : Real :=
  ∑ b : Fin (k + 1), quantumIsingChainInteraction (L + 1) (sigma b)

noncomputable def quantumIsingBlockLongInteraction (k L : Nat)
    (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) : Real :=
  quantumIsingChainInteraction ((k + 1) * (L + 1))
    ((quantumIsingBlockEquiv (k + 1) (L + 1)).symm sigma)

end StatMech.FrontierA
