/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Def.v1.Atlas.TensorCategories.code.Theorem_1_53_1
set_option maxHeartbeats 400000
set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u v w


section CartanMatrix

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Data of a pivotal structure on a rigid monoidal category: a natural family of
isomorphisms `V ≅ V**` compatible with morphisms via double duality. -/
structure PivotalStructureData (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [RigidCategory C] where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ

end CartanMatrix
