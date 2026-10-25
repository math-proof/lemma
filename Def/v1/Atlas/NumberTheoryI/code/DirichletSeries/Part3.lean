/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula
import Theorem.v1.Atlas.NumberTheoryI.code.DirichletSeries.Part2


noncomputable section

open scoped Classical

namespace ArakelovDivisor

variable {K : Type*} [Field K] {hG : IsGlobalField K}

def sizeHom : ArakelovDivisor K hG →* ℝ where
  toFun := size
  map_one' := size_one
  map_mul' := size_mul

end ArakelovDivisor
end
