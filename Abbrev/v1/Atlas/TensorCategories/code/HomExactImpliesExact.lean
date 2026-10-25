/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HomExactImpliesExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
import Structure.v1.Atlas.TensorCategories.code.HomExactImpliesExact.Part2
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- Existence of internal-Hom data for any left `C`-module category `M`. -/
abbrev proposition_2_10_7_part1
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  prop_2_10_7_hom_exact_implies_exact h

end CategoryTheory
