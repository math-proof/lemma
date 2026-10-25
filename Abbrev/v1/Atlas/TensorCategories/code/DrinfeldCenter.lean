/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DrinfeldCenter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.DualCategory.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.DualCategory
open CategoryTheory


/-- Definition 2.14.13 (the Drinfeld center `Z(C)`): the dual category of `C` over its
enveloping category `C ⊠ C^{op}`. -/
abbrev Definition_2_14_13 (C : Type u) [Category.{v} C] [MonoidalCategory C] :=
  DualCatObj (EnvelopingCategory C) C

