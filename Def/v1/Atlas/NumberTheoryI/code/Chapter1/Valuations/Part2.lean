/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/Valuations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.NumberTheoryI.code.Chapter1.Valuations


noncomputable section

def discreteValuationAbsoluteValue {k : Type*} [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    {c : NNReal} (hc : 1 < c) : AbsoluteValue k ℝ where
  toFun x := discreteValuationAbsoluteValueFun v (ne_zero_of_lt hc) x
  map_mul' _ _ := by simp [discreteValuationAbsoluteValueFun]
  nonneg' _ := NNReal.coe_nonneg _
  eq_zero' _ := by simp [discreteValuationAbsoluteValueFun]
  add_le' _ _ :=
    (isNonarchimedean_discreteValuationAbsoluteValueFun v hc).add_le fun _ => bot_le

end
