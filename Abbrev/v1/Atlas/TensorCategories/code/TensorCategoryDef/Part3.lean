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
import Instance.v1.Atlas.TensorCategories.code.TensorCategoryDef
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe v u


namespace TensorCategories

attribute [instance] LocallyFiniteCategory.homFinite

/-- Definition 1.12.3 alias: a multitensor category. -/
abbrev Definition_1_12_3_MultitensorCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  MultitensorCategory k C

/-- Definition 1.12.3 alias: a tensor category. -/
abbrev Definition_1_12_3_TensorCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  TensorCategory k C

/-- Definition 1.12.3 alias: a multifusion category. -/
abbrev Definition_1_12_3_MultifusionCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  MultifusionCategory k C

/-- Definition 1.12.3 alias: a fusion category. -/
abbrev Definition_1_12_3_FusionCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  FusionCategory k C

/-- Definition 1.12.3 alias (snake-case): a multitensor category. -/
abbrev def_1_12_3_multitensor (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  MultitensorCategory k C

/-- Definition 1.12.3 alias (snake-case): a tensor category. -/
abbrev def_1_12_3_tensor (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  TensorCategory k C

/-- Definition 1.12.3 alias: default multitensor category Prop. -/
abbrev def_1_12_3 (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop :=
  MultitensorCategory k C

end TensorCategories

/-- Definition 1.12.1 alias (snake-case, top-level): a locally finite `k`-linear abelian category. -/
abbrev def_1_12_1_locally_finite_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C] :=
  TensorCategories.LocallyFiniteCategory k C

/-- Definition 1.13.3 alias (snake-case, top-level): a multiring category. -/
abbrev def_1_13_3_multiring_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  TensorCategories.MultiringCategory k C

/-- Definition 1.13.3 alias (snake-case, top-level): a ring category. -/
abbrev def_1_13_3_ring_category (k : Type*) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] :=
  TensorCategories.RingCategory k C

