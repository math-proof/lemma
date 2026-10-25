/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HomExactImpliesExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
import Class.v1.Atlas.TensorCategories.code.HomExactImpliesExact
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- Data witnessing the internal-Hom adjunction `Hom(X ⊗ m, n) ≃ Hom(X, iHom m n)` together
with the second-variable exactness assumption that `iHom m -` preserves both monos and epis. -/
structure InternalHomExactInSecondVar
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] where
  iHom : M → M → C
  iHomEquiv : ∀ (X : C) (m n : M), (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ iHom m n)
  iHomMap : ∀ (m : M) {n₁ n₂ : M}, (n₁ ⟶ n₂) → (iHom m n₁ ⟶ iHom m n₂)
  preserves_mono : ∀ (m : M) {n₁ n₂ : M} (f : n₁ ⟶ n₂), Mono f → Mono (iHomMap m f)
  preserves_epi : ∀ (m : M) {n₁ n₂ : M} (f : n₁ ⟶ n₂), Epi f → Epi (iHomMap m f)
  iHomEquiv_natural : ∀ (X : C) (m : M) {n₁ n₂ : M} (g : X ⊗ᵐ m ⟶ n₁) (f : n₁ ⟶ n₂),
    iHomEquiv X m n₂ (g ≫ f) = (iHomEquiv X m n₁ g) ≫ (iHomMap m f)

end CategoryTheory
