/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CoxeterTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Lemma.Int.IsInQPlus0
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9


noncomputable section

open scoped BigOperators

namespace CoxeterGroupData

variable (C : CoxeterGroupData)

structure ReducedWord (w : C.W) where
  word : List C.W
  mem_simple : ∀ s ∈ word, s ∈ C.simpleReflections
  prod_eq : word.prod = w
  length_eq : word.length = C.length w

end CoxeterGroupData
end
