/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingBlockLongSeamInteraction (k L : Nat)
    (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) : Real :=
  (∑ b : Fin k,
    quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
      quantumIsingSpinSign (sigma b.succ 0)) +
    quantumIsingSpinSign (sigma (Fin.last k) (Fin.last L)) *
      quantumIsingSpinSign (sigma 0 0)

end StatMech.FrontierA
