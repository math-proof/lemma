/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexVertex


namespace StatMech.Universality

open Complex


theorem hexOmega_sq :
    hexOmega ^ 2 = Complex.exp (((2 * (2 * Real.pi / 3) : ℝ) : ℂ) * Complex.I) := by
  unfold hexOmega
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring


end StatMech.Universality
