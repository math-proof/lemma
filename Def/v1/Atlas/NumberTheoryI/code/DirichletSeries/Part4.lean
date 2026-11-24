module
public import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula
public import Theorem.v1.Atlas.NumberTheoryI.code.DirichletSeries.Part3


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

def L (c : ArakelovDivisor K hG) : Set K :=
  {x : K | ∀ v, hG.normAbsVal v x ≤ c.val v}

end ArakelovDivisor
end
