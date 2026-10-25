/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolReduction


namespace StatMech.FrontierA

noncomputable def quantumIsingTrotterReducedParameter
    (beta h : Real) (n : Nat) (k : Real) : Real :=
  let t := beta / (2 * n)
  let x := beta * h / (2 * n)
  Real.cosh t * ((1 + x ^ 2) / (1 - x ^ 2)) +
    Real.sinh t * (2 * x / (1 - x ^ 2)) * Real.cos k

end StatMech.FrontierA
