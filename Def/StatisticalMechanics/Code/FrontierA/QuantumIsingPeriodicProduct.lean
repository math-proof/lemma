/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingPeriodicProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicProduct.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingPeriodicRoot (n : Nat) (j : Nat) : Complex :=
  Complex.exp (2 * Real.pi * Complex.I / n) ^ j

end StatMech.FrontierA
