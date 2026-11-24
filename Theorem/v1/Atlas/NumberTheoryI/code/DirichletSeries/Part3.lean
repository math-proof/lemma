module
public import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula
public import Def.v1.Atlas.NumberTheoryI.code.DirichletSeries.Part3


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

@[simp] theorem sizeHom_apply (c : ArakelovDivisor K hG) :
    sizeHom c = c.size := rfl

end ArakelovDivisor
end
