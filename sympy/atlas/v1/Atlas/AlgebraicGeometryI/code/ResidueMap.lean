/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueMap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

noncomputable section

namespace LaurentSeries

open HahnSeries

variable (k : Type*) [Field k]

/-- The residue `k`-linear map on Laurent series: extracting the coefficient of `t^{-1}`,
the algebraic incarnation of the analytic residue at the origin. -/
def residue : LaurentSeries k →ₗ[k] k :=
  HahnSeries.coeff.linearMap (-1 : ℤ)

variable {k}
