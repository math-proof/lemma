/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InvertibleObjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Class.v1.Atlas.TensorCategories.code.InvertibleObjects
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The unit object `𝟙_ C` is invertible, with itself as tensor inverse and the left
unitor as both compositional isomorphisms. -/
@[reducible]
def unit_invertible : IsInvertibleObject (𝟙_ C) where
  tensorInverse := 𝟙_ C
  compIso := λ_ (𝟙_ C)
  invCompIso := λ_ (𝟙_ C)

variable [RigidCategory C]

/-- Definition 1.11.1: in a rigid category, an object `X` is invertible iff both the
evaluation `ε_ X Xᘁ` and the coevaluation `η_ X Xᘁ` are isomorphisms. -/
def Definition_1_11_1_InvertibleObject (X : C) : Prop :=
  IsIso (ε_ X (Xᘁ)) ∧ IsIso (η_ X (Xᘁ))

/-- Construct an `IsInvertibleObject` instance for `X` from its right dual `Xᘁ` together
with isomorphisms `X ⊗ Xᘁ ≅ 𝟙_ C` and `Xᘁ ⊗ X ≅ 𝟙_ C`. -/
@[reducible]
def IsInvertibleObject.ofRightDual (X : C) [HasRightDual X]
    (h1 : X ⊗ (Xᘁ) ≅ 𝟙_ C) (h2 : (Xᘁ) ⊗ X ≅ 𝟙_ C) : IsInvertibleObject X where
  tensorInverse := Xᘁ
  compIso := h1
  invCompIso := h2

/-- The tensor inverse of an invertible object is itself invertible, with `X` as its
inverse. -/
@[reducible]
def IsInvertibleObject.inverseInvertible (X : C) [h : IsInvertibleObject X] :
    IsInvertibleObject h.tensorInverse where
  tensorInverse := X
  compIso := h.invCompIso
  invCompIso := h.compIso

/-- If the tensor inverse of an invertible object `X` equals its right dual `Xᘁ`, then
`Xᘁ` is itself invertible. -/
@[reducible]
def rightDual_invertible (X : C) [HasRightDual X]
    (hX : IsInvertibleObject X) (h : hX.tensorInverse = Xᘁ) :
    IsInvertibleObject (Xᘁ : C) :=
  h ▸ hX.inverseInvertible

/-- Given inverse isomorphisms `X ⊗ Xi ≅ 𝟙_ C` and `Y ⊗ Yi ≅ 𝟙_ C`, build the
isomorphism `(X ⊗ Y) ⊗ (Yi ⊗ Xi) ≅ 𝟙_ C` via the associators and unitors. -/
noncomputable def tensorCompIso {X Y Xi Yi : C}
    (hX : X ⊗ Xi ≅ 𝟙_ C) (hY : Y ⊗ Yi ≅ 𝟙_ C) :
    (X ⊗ Y) ⊗ (Yi ⊗ Xi) ≅ 𝟙_ C :=
  (α_ X Y (Yi ⊗ Xi)) ≪≫
  (tensorLeft X).mapIso (α_ Y Yi Xi).symm ≪≫
  (tensorLeft X).mapIso (tensorIso hY (Iso.refl Xi)) ≪≫
  (tensorLeft X).mapIso (λ_ Xi) ≪≫
  hX

/-- Given inverse isomorphisms `Xi ⊗ X ≅ 𝟙_ C` and `Yi ⊗ Y ≅ 𝟙_ C`, build the
isomorphism `(Yi ⊗ Xi) ⊗ (X ⊗ Y) ≅ 𝟙_ C` via the associators and unitors. -/
noncomputable def tensorInvCompIso {X Y Xi Yi : C}
    (hX : Xi ⊗ X ≅ 𝟙_ C) (hY : Yi ⊗ Y ≅ 𝟙_ C) :
    (Yi ⊗ Xi) ⊗ (X ⊗ Y) ≅ 𝟙_ C :=
  (α_ Yi Xi (X ⊗ Y)) ≪≫
  (tensorLeft Yi).mapIso (α_ Xi X Y).symm ≪≫
  (tensorLeft Yi).mapIso (tensorIso hX (Iso.refl Y)) ≪≫
  (tensorLeft Yi).mapIso (λ_ Y) ≪≫
  hY

/-- The tensor product `X ⊗ Y` of two invertible objects is invertible, with tensor
inverse `Y⁻¹ ⊗ X⁻¹`. -/
@[reducible]
noncomputable def tensor_invertible (X Y : C)
    [hX : IsInvertibleObject X] [hY : IsInvertibleObject Y] :
    IsInvertibleObject (X ⊗ Y) where
  tensorInverse := hY.tensorInverse ⊗ hX.tensorInverse
  compIso := tensorCompIso hX.compIso hY.compIso
  invCompIso := tensorInvCompIso hX.invCompIso hY.invCompIso

end CategoryTheory
