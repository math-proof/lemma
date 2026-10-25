/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


noncomputable def hexUnit (h : ℤ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)))


end StatMech.Universality
