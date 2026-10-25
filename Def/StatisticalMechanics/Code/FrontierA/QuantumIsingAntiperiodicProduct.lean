/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.KummerExtension
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingAntiperiodicRoot (n : Nat) (j : Nat) : Complex :=
  Complex.exp (2 * Real.pi * Complex.I / n) ^ j *
    Complex.exp (Real.pi * Complex.I / n)

end StatMech.FrontierA
