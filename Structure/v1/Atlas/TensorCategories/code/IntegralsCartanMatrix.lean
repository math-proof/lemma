/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.IntegralsDefs
public import Theorem.Category.Atlas.v1.TensorCategories.code.IntegralsDefs
public import Theorem.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Instance.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2
public import Mathlib.RingTheory.SimpleModule.Basic
public import Def.v1.Atlas.TensorCategories.code.IntegralsCartanMatrix.Part2
public section

set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section CartanMatrix

open CategoryTheory MonoidalCategory

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Data of a pivotal structure on a rigid monoidal category: a natural isomorphism
`Id ≅ ?**` (Definition 1.38.1). -/
structure PivotalStructureData (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [RigidCategory C] where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ

end CartanMatrix
