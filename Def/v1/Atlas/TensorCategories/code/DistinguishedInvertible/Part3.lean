/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.CategoryTheory.Yoneda
public import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
public import Theorem.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
public import Theorem.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
public import Class.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2

@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits TensorCategories

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]


/-- Construct a `HasDoubleDualExtension` instance from a canonical choice of pivotal-style
data already defined on all objects of `C`. -/
@[reducible] noncomputable def hasDoubleDualExtensionOfCanonical
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (j : ∀ (X : C), X ≅ (Xᘁ)ᘁ)
    (j_nat : ∀ {V W : C} (f : V ⟶ W), f ≫ (j W).hom = (j V).hom ≫ (fᘁ)ᘁ)
    (tc : ∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ)
    (j_mon : ∀ (V W : C), (j (V ⊗ W)).hom = ((j V).hom ⊗ₘ (j W).hom) ≫ (tc V W).hom)
    (j_dimUnit : TensorCategories.leftQuantumTrace C (j (𝟙_ C)).hom = 𝟙 (𝟙_ C))
    : HasDoubleDualExtension C where
  extend_pivotalIso _ := j
  extend_pivotalIso_natural _ := j_nat
  extend_tensorCoherenceIso _ := tc
  extend_monoidality _ := j_mon
  extend_dimUnit _ := j_dimUnit

end CategoryTheory
