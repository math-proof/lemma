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
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part2
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe v u


namespace TensorCategories

attribute [instance] LocallyFiniteCategory.homFinite

/-- A preadditive category is semisimple if every object is isomorphic to a finite biproduct
of simple objects. -/
class IsSemisimpleCategory (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroMorphisms C] : Prop where
  semisimple : ∀ (X : C), ∃ (n : ℕ) (Y : Fin n → C) (_ : ∀ i, Simple (Y i))
    (_ : HasBiproduct Y), Nonempty (X ≅ ⨁ Y)

/-- A category has finitely many simple objects if there exists a finite list of simples
representing every isomorphism class of simple objects. -/
class HasFinitelyManySimples (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] : Prop where
  finiteSimples : ∃ (n : ℕ) (S : Fin n → C), (∀ i, Simple (S i)) ∧
    (∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ S i))

/-- Definition 1.12.3: a multifusion category is a semisimple multitensor category with
finitely many isomorphism classes of simple objects. -/
class MultifusionCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop extends MultitensorCategory k C where
  semisimple : IsSemisimpleCategory C
  hasFinitelyManySimples : HasFinitelyManySimples C

/-- Definition 1.12.3: a fusion category is a semisimple tensor category with finitely many
isomorphism classes of simple objects. -/
class FusionCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] : Prop extends TensorCategory k C where
  semisimple : IsSemisimpleCategory C
  hasFinitelyManySimples : HasFinitelyManySimples C

end TensorCategories
