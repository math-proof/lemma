/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula
import Instance.v1.Atlas.NumberTheoryI.code.DirichletSeries.Part2


noncomputable section

open scoped Classical

namespace ArakelovDivisor

variable {K : Type*} [Field K] {hG : IsGlobalField K}

def principal (x : K) (hx : x ≠ 0) : ArakelovDivisor K hG where
  val := fun v => hG.normAbsVal v x
  pos := by
    intro v
    rw [hG.normAbsVal_eq]
    exact Real.rpow_pos_of_pos ((hG.absVal v).pos hx) _
  finite_support := hG.normAbsVal_eq_one_of_finite x hx

def size (c : ArakelovDivisor K hG) : ℝ :=
  ∏ᶠ v, c.val v

end ArakelovDivisor
end
