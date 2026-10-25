/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HomExactImpliesExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
import Abbrev.v1.Atlas.TensorCategories.code.HomExactImpliesExact
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- Restatement of Proposition 2.10.7(2) as an alias of
`prop_2_10_7_all_functors_exact_implies_exact`. -/
@[reducible] noncomputable def proposition_2_10_7
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  proposition_2_10_7_part1 h

end CategoryTheory
