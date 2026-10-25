/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hlhr_orientedSpan (f : ℕ → ℝ) (up : Bool)
    (lo hi : ℕ) : ℝ :=
  hlhr_signed up (f hi) - hlhr_signed up (f lo)


end StatMech.Universality
