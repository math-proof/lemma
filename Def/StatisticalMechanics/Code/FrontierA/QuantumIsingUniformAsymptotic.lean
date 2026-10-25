/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformAsymptotic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductReduction
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolAsymptotic.Part2
import Mathlib.Topology.UniformSpace.UniformConvergence
open Filter
open scoped Topology


namespace StatMech.FrontierA

noncomputable def quantumIsingScaledReducedParameter
    (beta h : Real) (n : Nat) (k : Real) : Real :=
  (n + 1 : Real) ^ 2 *
    (quantumIsingTrotterReducedParameter beta h (n + 1) k - 1)

noncomputable def quantumIsingScaledReducedLimit
    (beta h k : Real) : Real :=
  beta ^ 2 / 8 * quantumIsingDispersion h k ^ 2

end StatMech.FrontierA
