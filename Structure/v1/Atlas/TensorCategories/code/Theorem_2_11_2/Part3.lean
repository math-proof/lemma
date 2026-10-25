/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_2_11_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Equivalence
import Instance.v1.Atlas.TensorCategories.code.Theorem_2_11_2
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory

attribute [reassoc (attr := simp)] RModHom₂.comm

/-- Data for the internal-Hom setup of Theorem 2.11.2: a chosen generator
`gen ∈ M`, the action functor `C ⥤ M`, the internal endomorphism algebra `A`,
and the corresponding functor `M ⥤ ModC₂ A` together with the natural identification
of the composition with the free-module functor. -/
structure InternalHomData₂ (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] where
  gen : M
  actOnGen : C ⥤ M
  endAlg : AlgObj₂ C
  F : M ⥤ ModC₂ endAlg
  freeModule : C ⥤ ModC₂ endAlg
  moduleCompat : actOnGen ⋙ F ≅ freeModule

/-- Right-exactness hypothesis on the internal-Hom functor `F = Hom(M, -)`. -/
structure InternalHomRightExact₂
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M) : Prop where
  preservesEpi : ∀ {N₁ N₂ : M} (f : N₁ ⟶ N₂), Epi f → Epi (hom.F.map f)

/-- Generation hypothesis: every object of `M` admits an epimorphism from some
`X ⊗ M` (i.e. `hom.actOnGen.obj X`). -/
structure InternalHomGeneration₂
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M) : Prop where
  generation : ∀ (N : M), ∃ (X : C) (f : hom.actOnGen.obj X ⟶ N), Epi f

end CategoryTheory
