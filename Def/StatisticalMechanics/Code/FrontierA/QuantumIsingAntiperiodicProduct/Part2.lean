/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.KummerExtension
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicProduct
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingAntiperiodicAngle (n : Nat) (j : Nat) : Real :=
  (2 * (j : Real) + 1) * Real.pi / n

end StatMech.FrontierA
