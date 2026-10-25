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
import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

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
