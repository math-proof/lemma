/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

noncomputable def quantumIsingTwoBlockPeriodicInteraction (A B : Nat)
    (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) : Real :=
  quantumIsingChainInteraction (A + 1) pair.1 +
    quantumIsingChainInteraction (B + 1) pair.2

noncomputable def quantumIsingTwoBlockLongInteraction (A B : Nat)
    (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) : Real :=
  quantumIsingChainInteraction ((A + 1) + (B + 1))
    ((quantumIsingSumBlockEquiv (A + 1) (B + 1)).symm pair)

noncomputable def quantumIsingTwoBlockOpenInteraction (A B : Nat)
    (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) : Real :=
  (∑ i : Fin A,
    quantumIsingSpinSign (pair.1 i.castSucc) *
      quantumIsingSpinSign (pair.1 i.succ)) +
  (∑ j : Fin B,
    quantumIsingSpinSign (pair.2 j.castSucc) *
      quantumIsingSpinSign (pair.2 j.succ))

end StatMech.FrontierA
