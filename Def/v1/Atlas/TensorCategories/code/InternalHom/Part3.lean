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
import Theorem.v1.Atlas.TensorCategories.code.InternalHom.Part2
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]

/-- The internal Hom adjunction equivalence
`(X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom m n)`, packaged as a standalone definition. -/
def moduleIHom_adjunction (X : C) (m n : M) :
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom (C := C) m n) :=
  moduleIHomEquiv X m n

/-- The natural isomorphism `Hom(𝟙_ C ⊗ᵐ m, n) ≅ Hom(m, n)` coming from the unit
isomorphism `actℓ_ m : 𝟙_ C ⊗ᵐ m ≅ m`. -/
def moduleIHom_unit_iso (m n : M) :
    moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ≅ moduleIHom m n where
  hom := moduleIHomEquiv _ m n
    ((moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n) ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n)
  inv := moduleIHomEquiv _ (𝟙_ C ⊗ᵐ m) n
    ((moduleIHom (C := C) m n) ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n)
  hom_inv_id := by
    apply (moduleIHomEquiv _ (𝟙_ C ⊗ᵐ m) n).symm.injective
    rw [moduleIHomEquiv_symm_eq, actWhiskerRight_comp, assoc]
    have h1 : (moduleIHomEquiv _ (𝟙_ C ⊗ᵐ m) n
          (moduleIHom (C := C) m n ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n)) ▷ᵐ (𝟙_ C ⊗ᵐ m) ≫
        moduleIHomEv (𝟙_ C ⊗ᵐ m) n =
        moduleIHom (C := C) m n ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n := by
      rw [← moduleIHomEquiv_symm_eq, Equiv.symm_apply_apply]
    rw [h1, actWhisker_interchange_assoc]
    have h2 : (moduleIHomEquiv _ m n
          (moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n)) ▷ᵐ m ≫
        moduleIHomEv m n =
        moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n := by
      rw [← moduleIHomEquiv_symm_eq, Equiv.symm_apply_apply]
    rw [h2, ← actWhiskerLeft_comp_assoc, Iso.hom_inv_id,
      LeftModuleCategory.actWhiskerLeft_id, id_comp]
    rfl
  inv_hom_id := by
    apply (moduleIHomEquiv _ m n).symm.injective
    rw [moduleIHomEquiv_symm_eq, actWhiskerRight_comp, assoc]
    have h1 : (moduleIHomEquiv _ m n
          (moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n)) ▷ᵐ m ≫
        moduleIHomEv m n =
        moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n := by
      rw [← moduleIHomEquiv_symm_eq, Equiv.symm_apply_apply]
    rw [h1, actWhisker_interchange_assoc]
    have h2 : (moduleIHomEquiv _ (𝟙_ C ⊗ᵐ m) n
          (moduleIHom (C := C) m n ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n)) ▷ᵐ (𝟙_ C ⊗ᵐ m) ≫
        moduleIHomEv (𝟙_ C ⊗ᵐ m) n =
        moduleIHom (C := C) m n ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n := by
      rw [← moduleIHomEquiv_symm_eq, Equiv.symm_apply_apply]
    rw [h2, ← actWhiskerLeft_comp_assoc, Iso.inv_hom_id,
      LeftModuleCategory.actWhiskerLeft_id, id_comp]
    rfl

/-- Curry equivalence: `(T ⊗ X ⟶ Hom(m, n)) ≃ (T ⟶ Hom(X ⊗ᵐ m, n))`, obtained by
combining the internal Hom adjunction with the action associator. -/
def moduleIHom_curry_equiv (T X : C) (m n : M) :
    (T ⊗ X ⟶ moduleIHom (C := C) m n) ≃ (T ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) :=
  ((moduleIHomEquiv (T ⊗ X) m n).symm.trans
    (Equiv.mk
      (fun (f : (T ⊗ X) ⊗ᵐ m ⟶ n) => (actμ_ T X m).inv ≫ f)
      (fun (g : T ⊗ᵐ (X ⊗ᵐ m) ⟶ n) => (actμ_ T X m).hom ≫ g)
      (fun f => by simp)
      (fun g => by simp))).trans
    (moduleIHomEquiv T (X ⊗ᵐ m) n)

/-- Tensor equivalence: `(Y ⟶ Hom(X ⊗ᵐ m, n)) ≃ (Y ⟶ Hom(m, n) ⊗ Xᘁ)` when `X` has a
right dual, obtained from `moduleIHom_curry_equiv` and `tensorRightHomEquiv`. -/
def moduleIHom_tensor_equiv (Y X : C) [HasRightDual X] (m n : M) :
    (Y ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) ≃ (Y ⟶ moduleIHom (C := C) m n ⊗ Xᘁ) :=
  (moduleIHom_curry_equiv Y X m n).symm.trans (tensorRightHomEquiv Y X Xᘁ (moduleIHom m n))

end CategoryTheory
