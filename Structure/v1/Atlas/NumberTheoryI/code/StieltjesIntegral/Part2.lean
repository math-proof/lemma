/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Def.v1.Atlas.NumberTheoryI.code.StieltjesIntegral


namespace RiemannStieltjes

variable {a b : ℝ}

structure TaggedPartition (a b : ℝ) extends IntervalPartition a b where
  tags : Fin n → ℝ
  tag_mem : ∀ (k : Fin n),
    pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ ≤ tags k ∧
    tags k ≤ pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩

end RiemannStieltjes
