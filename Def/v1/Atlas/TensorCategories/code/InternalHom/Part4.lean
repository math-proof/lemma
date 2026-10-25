/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Theorem.v1.Atlas.TensorCategories.code.InternalHom.Part3
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]

/-- The natural isomorphism `Hom(X ⊗ᵐ m, n) ≅ Hom(m, n) ⊗ Xᘁ` produced from
`moduleIHom_tensor_equiv` (Lemma 2.10.4 part 3). -/
def moduleIHom_curry_iso (X : C) [HasRightDual X] (m n : M) :
    moduleIHom (C := C) (X ⊗ᵐ m) n ≅ moduleIHom (C := C) m n ⊗ Xᘁ where
  hom := moduleIHom_tensor_equiv _ X m n (𝟙 _)
  inv := (moduleIHom_tensor_equiv _ X m n).symm (𝟙 _)
  hom_inv_id := by


    apply (moduleIHom_tensor_equiv _ X m n).injective
    rw [moduleIHom_tensor_equiv_natural]
    simp [Equiv.apply_symm_apply]
  inv_hom_id := by


    apply (moduleIHom_tensor_equiv _ X m n).symm.injective
    have h_nat_symm : ∀ {A B : C} (f : A ⟶ B) (g : B ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n),
        (moduleIHom_tensor_equiv _ X m n).symm
          (f ≫ moduleIHom_tensor_equiv B X m n g) = f ≫ g := by
      intro A B f g
      conv_rhs => rw [← Equiv.symm_apply_apply (moduleIHom_tensor_equiv A X m n) (f ≫ g)]
      congr 1
      exact (moduleIHom_tensor_equiv_natural f g).symm
    simp only [h_nat_symm, comp_id]

/-- Left inverse condition for `modTensorHomEquiv`: applying the unit-evaluation pair
recovers the original morphism `f : N ⟶ X ⊗ᵐ P`. -/
def lemma_2_10_4_part1 (X : C) (m n : M) :
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom (C := C) m n) :=
  moduleIHom_adjunction X m n

/-- Lemma 2.10.4 part 2: when `X` is rigid, morphisms `m₁ ⟶ X ⊗ᵐ m₂` correspond to
global sections of `X ⊗ Hom(m₁, m₂)`. -/
def lemma_2_10_4_part3 (X : C) [HasRightDual X] (m n : M) :
    moduleIHom (C := C) (X ⊗ᵐ m) n ≅ moduleIHom m n ⊗ Xᘁ :=
  moduleIHom_curry_iso X m n

/-- Lemma 2.10.4 part 4: when `X` is rigid, `Hom(m₁, X ⊗ᵐ m₂) ≅ X ⊗ Hom(m₁, m₂)`. -/
def moduleIHomMapRight (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂') :
    moduleIHom (C := C) m₁ m₂ ⟶ moduleIHom m₁ m₂' :=
  moduleIHomEquiv (moduleIHom m₁ m₂) m₁ m₂' (moduleIHomEv m₁ m₂ ≫ f)

/-- Contravariant functorial action of `moduleIHom` in the left argument:
`Hom(m₁', m₂) ⟶ Hom(m₁, m₂)` induced by `f : m₁ ⟶ m₁'`. -/
def moduleIHomMapLeft {m₁ m₁' : M} (f : m₁ ⟶ m₁') (m₂ : M) :
    moduleIHom (C := C) m₁' m₂ ⟶ moduleIHom m₁ m₂ :=
  moduleIHomEquiv (moduleIHom m₁' m₂) m₁ m₂
    ((moduleIHom (C := C) m₁' m₂) ◁ᵐ f ≫ moduleIHomEv m₁' m₂)

end CategoryTheory
