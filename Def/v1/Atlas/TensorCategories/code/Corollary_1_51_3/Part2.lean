/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_51_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Yoneda
public import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
public import Theorem.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
public import Class.v1.Atlas.TensorCategories.code.Corollary_1_51_3

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v u


namespace CategoryTheory

section TensorDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

variable [HasDistinguishedInvData C]

/-- The distinguished invertible object `L_ρ` of `C` supplied by `HasDistinguishedInvData`. -/
def distinguishedObj : C := HasDistinguishedInvData.distinguished (C := C)

end TensorDual
end CategoryTheory
