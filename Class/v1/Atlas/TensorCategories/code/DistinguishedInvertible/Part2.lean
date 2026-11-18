module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
public import Structure.v1.Atlas.TensorCategories.code.DistinguishedInvertible
public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits TensorCategories

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

variable (C) in
/-- Data needed to extend a pivotal-style structure from projective objects to all of `C`:
a way to extend a natural isomorphism `P ≅ P^{**}` (for projective `P`) to all objects,
together with the required naturality, monoidality, and unit-trace conditions. -/
class HasDoubleDualExtension where
  extend_pivotalIso :
    (∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) →
    (∀ (X : C), X ≅ (Xᘁ)ᘁ)
  extend_pivotalIso_natural :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P))
      {V W : C} (f : V ⟶ W),
    f ≫ (extend_pivotalIso hProj W).hom =
      (extend_pivotalIso hProj V).hom ≫ (fᘁ)ᘁ
  extend_tensorCoherenceIso :
    (∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) →
    (∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ)
  extend_monoidality :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P))
      (V W : C),
    (extend_pivotalIso hProj (V ⊗ W)).hom =
      ((extend_pivotalIso hProj V).hom ⊗ₘ (extend_pivotalIso hProj W).hom) ≫
        (extend_tensorCoherenceIso hProj V W).hom
  extend_dimUnit :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)),
    TensorCategories.leftQuantumTrace C (extend_pivotalIso hProj (𝟙_ C)).hom = 𝟙 (𝟙_ C)

end CategoryTheory
