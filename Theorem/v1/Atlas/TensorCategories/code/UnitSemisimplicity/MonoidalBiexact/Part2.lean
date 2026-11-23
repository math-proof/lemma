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
public import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

public section

universe v u w


noncomputable section

namespace TensorCategories

section TensorNilpotent

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- If an endomorphism `f` of the unit object squares to zero under composition,
then its tensor square `f ⊗ₘ f` is the zero morphism. -/
theorem tensorHom_sq_of_sq_zero (f : 𝟙_ C ⟶ 𝟙_ C) (hf : f ≫ f = 0) :
    f ⊗ₘ f = 0 := by
  have hom_eq : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by monoidal_coherence
  have h1 : (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ f) ≫ (ρ_ (𝟙_ C)).hom = f ≫ f := by
    rw [rightUnitor_inv_comp_tensorHom_assoc, ← hom_eq, leftUnitor_naturality, hom_eq]; simp
  rw [hf] at h1
  rw [← cancel_epi (ρ_ (𝟙_ C)).inv, ← cancel_mono (ρ_ (𝟙_ C)).hom]
  simp [h1]

end TensorNilpotent
end TensorCategories
end
