/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Def.v1.Atlas.TensorCategories.code.TensorExact.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorExact
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Subobject.Lattice
import Class.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part2
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe v u


namespace TensorCategories

attribute [instance] LocallyFiniteCategory.homFinite

/-- Definition 1.13.3 alias: a multiring category. -/
abbrev Definition_1_13_3_MultiringCategory (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  MultiringCategory k C

/-- Definition 1.13.3 alias: a ring category. -/
abbrev Definition_1_13_3_RingCategory (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  RingCategory k C

/-- Definition 1.13.3 alias (snake-case): a multiring category. -/
abbrev def_1_13_3_multiring_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  MultiringCategory k C

/-- Definition 1.13.3 alias (snake-case): a ring category. -/
abbrev def_1_13_3_ring_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  RingCategory k C

end TensorCategories
