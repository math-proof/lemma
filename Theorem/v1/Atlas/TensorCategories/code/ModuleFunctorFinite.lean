/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
set_option maxHeartbeats 800000

open CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-- The category of module functors between two left `C`-module categories carries a
canonical abelian structure. -/


