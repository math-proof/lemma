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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part27


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


structure HLHRStripColumnRealization (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) where
  column : (p : ℕ × ℕ) → p ∈ hlhr_literalIntervals h0 ts → ℕ
  column_pos : ∀ p hp, 0 < column p hp
  span_strict : ∀ p hp q hq,
    hlhr_intervalSpan (hlhr_height h0 ts) p >
        hlhr_intervalSpan (hlhr_height h0 ts) q →
      column p hp > column q hq

end StatMech.Universality
