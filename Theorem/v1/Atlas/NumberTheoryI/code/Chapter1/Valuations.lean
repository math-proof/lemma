/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/Valuations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.Chapter1.Valuations


noncomputable section

lemma isNonarchimedean_discreteValuationAbsoluteValueFun {k : Type*} [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    {c : NNReal} (hc : 1 < c) :
    IsNonarchimedean (discreteValuationAbsoluteValueFun v (ne_zero_of_lt hc)) := by
  intro x y
  simp only [discreteValuationAbsoluteValueFun]
  have h_mono := (WithZeroMulInt.toNNReal_strictMono hc).monotone
  rw [← h_mono.map_max]
  exact h_mono (v.map_add x y)

end
