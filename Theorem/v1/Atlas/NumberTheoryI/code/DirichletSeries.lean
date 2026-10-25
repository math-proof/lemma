/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula
import Instance.v1.Atlas.NumberTheoryI.code.DirichletSeries


noncomputable section

open scoped Classical

namespace ArakelovDivisor

variable {K : Type*} [Field K] {hG : IsGlobalField K}

@[simp] theorem one_val (v : hG.PlaceType) : (1 : ArakelovDivisor K hG).val v = 1 := rfl

@[simp] theorem mul_val (c d : ArakelovDivisor K hG) (v : hG.PlaceType) :
    (c * d).val v = c.val v * d.val v := rfl

@[simp] theorem inv_val (c : ArakelovDivisor K hG) (v : hG.PlaceType) :
    c⁻¹.val v = (c.val v)⁻¹ := rfl

@[ext] theorem ext {c d : ArakelovDivisor K hG} (h : ∀ v, c.val v = d.val v) : c = d := by
  cases c; cases d; simp only [mk.injEq]; ext v; exact h v

end ArakelovDivisor
end
