/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.CategoryTheory.Yoneda
import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
import Class.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2
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
