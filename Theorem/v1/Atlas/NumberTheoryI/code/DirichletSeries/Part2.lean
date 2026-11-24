module
public import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula
public import Def.v1.Atlas.NumberTheoryI.code.DirichletSeries.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped Classical

namespace ArakelovDivisor

variable {K : Type*} [Field K] {hG : IsGlobalField K}

@[simp] theorem size_one : (1 : ArakelovDivisor K hG).size = 1 := by
  simp [size, finprod_one]

theorem size_mul (c d : ArakelovDivisor K hG) :
    (c * d).size = c.size * d.size := by
  simp only [size, mul_val]
  exact finprod_mul_distrib c.hasFiniteMulSupport d.hasFiniteMulSupport

end ArakelovDivisor
end
