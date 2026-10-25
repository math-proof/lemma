/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexZConvClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


noncomputable def hzc_coeffWeight (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) : ℝ :=
  (hzc_sawCount a h0 n : ℝ) * x ^ n


end StatMech.Universality
