/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Def.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

universe w v u


namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section PivotalSection

variable [PivotalCategory C]

/-- Multiplicativity of the left quantum trace on tensor products. -/
structure Proposition_1_37_1 : Prop where
  left_eq_right_dual : ∀ {V : C} (a : V ⟶ (Vᘁ)ᘁ),
    leftQuantumTrace C a =
      η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)
  additivity : ∀ [Preadditive C] [HasBinaryBiproducts C] {V W : C}
    (a : V ⟶ (Vᘁ)ᘁ) (b : W ⟶ (Wᘁ)ᘁ)
    (ψ : (Vᘁ)ᘁ ⊞ (Wᘁ)ᘁ ≅ ((Limits.biprod V W)ᘁ : C)ᘁ),
    leftQuantumTrace C (Limits.biprod.lift (Limits.biprod.fst ≫ a) (Limits.biprod.snd ≫ b) ≫ ψ.hom) =
      leftQuantumTrace C a + leftQuantumTrace C b
  multiplicativity : ∀ {V W : C}
    (a : V ⟶ (Vᘁ)ᘁ) (b : W ⟶ (Wᘁ)ᘁ)
    (φ : (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ),
    leftQuantumTrace C ((a ⊗ₘ b) ≫ φ.hom) =
      leftQuantumTrace C a ≫ leftQuantumTrace C b
  cyclicity_left : ∀ {V : C} (a : V ⟶ (Vᘁ)ᘁ) (c : V ⟶ V),
    leftQuantumTrace C (c ≫ a) = leftQuantumTrace C (a ≫ (cᘁ)ᘁ)
  cyclicity_right : ∀ {V : C} (a : V ⟶ ᘁ(ᘁV)) (c : V ⟶ V),
    rightQuantumTrace C (c ≫ a) =
      rightQuantumTrace C (a ≫ leftAdjointMate (leftAdjointMate c))

/-- EGNO Proposition 1.38.5: the pivotal dimension is a character of the Grothendieck
ring (multiplicative on tensor products, additive on biproducts, and sending the unit to
1). -/
structure Proposition_1_38_5_IsCharacter [Preadditive C] [HasBinaryBiproducts C] : Prop where
  multiplicativity : ∀ (V W : C), pivotalDimension C (V ⊗ W) =
    pivotalDimension C V ≫ pivotalDimension C W
  additivity : ∀ (X Y : C), pivotalDimension C (Limits.biprod X Y) =
    pivotalDimension C X + pivotalDimension C Y
  unitality : pivotalDimension C (𝟙_ C) = 𝟙 (𝟙_ C)

end PivotalSection
end TensorCategories
