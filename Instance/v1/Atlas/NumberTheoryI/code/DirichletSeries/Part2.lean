/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula
public import Theorem.v1.Atlas.NumberTheoryI.code.DirichletSeries
@[expose] public section

noncomputable section

open scoped Classical

namespace ArakelovDivisor

variable {K : Type*} [Field K] {hG : IsGlobalField K}

instance : CommGroup (ArakelovDivisor K hG) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc a b c := by ext v; simp [mul_assoc]
  one_mul a := by ext v; simp
  mul_one a := by ext v; simp
  mul_comm a b := by ext v; simp [mul_comm]
  inv_mul_cancel a := by
    ext v
    show (a.val v)⁻¹ * a.val v = 1
    exact inv_mul_cancel₀ (ne_of_gt (a.pos v))

end ArakelovDivisor
end
