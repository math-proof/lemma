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
public import Def.v1.Atlas.NumberTheoryI.code.DirichletSeries
@[expose] public section

noncomputable section

open scoped Classical

namespace ArakelovDivisor

variable {K : Type*} [Field K] {hG : IsGlobalField K}

instance : One (ArakelovDivisor K hG) := ⟨one⟩

instance : Mul (ArakelovDivisor K hG) := ⟨mul⟩

instance : Inv (ArakelovDivisor K hG) := ⟨inv⟩

end ArakelovDivisor
end
