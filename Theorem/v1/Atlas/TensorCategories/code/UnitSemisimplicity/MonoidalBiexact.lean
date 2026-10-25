/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.RingTheory.Idempotents
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

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
