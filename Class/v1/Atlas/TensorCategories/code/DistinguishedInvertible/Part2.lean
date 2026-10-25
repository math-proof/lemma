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
import Structure.v1.Atlas.TensorCategories.code.DistinguishedInvertible
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
