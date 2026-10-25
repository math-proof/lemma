/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/LocallyFiniteDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


namespace TensorCategories

/-- Abbreviation for `LocallyFiniteCategory`: a `k`-linear abelian category is locally finite
if it is essentially small, all Hom spaces are finite dimensional, and every object has
finite length. -/
abbrev IsLocallyFinite (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C] :=
  LocallyFiniteCategory k C

/-- Definition 1.12.1: A `k`-linear abelian category is locally finite if it is essentially
small, all Hom spaces are finite dimensional, and every object has finite length. -/
abbrev Definition_1_12_1_LocallyFinite (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C] :=
  LocallyFiniteCategory k C

end TensorCategories
