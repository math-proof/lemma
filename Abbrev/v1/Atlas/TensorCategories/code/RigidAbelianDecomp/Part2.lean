/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidAbelianDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.MacLaneCoherence
import Lemma.Category.Atlas.v1.TensorCategories.code.MacLaneCoherence
import Lemma.Category.Atlas.v1.TensorCategories.code.MacLaneStrictness
import Lemma.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorExact
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Instance.v1.Atlas.TensorCategories.code.MacLaneStrictness.Part2
import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Def.v1.Atlas.TensorCategories.code.TensorExact.Part3
import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Def.v1.Atlas.TensorCategories.code.RigidAbelianDecomp
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory


/-- Reference abbreviation for the definition of a finite abelian category. -/
abbrev IsFiniteAbelianCategory_def := @IsFiniteAbelianCategory

