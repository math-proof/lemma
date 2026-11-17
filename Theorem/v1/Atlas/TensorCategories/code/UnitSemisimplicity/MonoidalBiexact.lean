/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.SimpleRing.Field
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.RingTheory.Idempotents
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

public section

universe v u w


noncomputable section

namespace TensorCategories

section EndUnitComm

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Endomorphisms of the unit object of a monoidal category commute (Proposition 1.2.7).
The proof uses coherence to identify the left and right unitors of the unit object. -/
theorem endUnit_comm (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  have hom_eq : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by monoidal_coherence
  have inv_eq : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by monoidal_coherence
  have h1 : (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ (𝟙_ C)).hom = f ≫ g := by
    rw [rightUnitor_inv_comp_tensorHom_assoc, ← hom_eq, leftUnitor_naturality, hom_eq]; simp
  have h2 : (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ (𝟙_ C)).hom = g ≫ f := by
    rw [← inv_eq, leftUnitor_inv_comp_tensorHom_assoc, rightUnitor_naturality]; simp [inv_eq]
  rw [← h1, h2]

end EndUnitComm
end TensorCategories
end
