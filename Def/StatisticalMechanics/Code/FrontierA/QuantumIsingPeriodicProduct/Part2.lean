/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingPeriodicProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicProduct.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingPeriodicProduct
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingPeriodicAngle (n : Nat) (j : Nat) : Real :=
  2 * (j : Real) * Real.pi / n

end StatMech.FrontierA
