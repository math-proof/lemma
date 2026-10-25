/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/Valuations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.NumberTheoryI.code.Chapter1.Valuations


noncomputable section

def discreteValuationAbsoluteValueFun {k : Type*} [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    {c : NNReal} (hc : c ≠ 0) (x : k) : NNReal :=
  (WithZeroMulInt.toNNReal hc) (v x)

end
