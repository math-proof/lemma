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
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part3
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]

/-- Naturality in `T` of the inverse curry equivalence:
`(curry^{-1} _ _ m n) (f ≫ g) = f ▷ X ≫ (curry^{-1} _ _ m n) g`. -/
theorem moduleIHom_curry_equiv_symm_natural {T₁ T₂ X : C} {m n : M}
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) :
    (moduleIHom_curry_equiv T₁ X m n).symm (f ≫ g) =
      f ▷ X ≫ (moduleIHom_curry_equiv T₂ X m n).symm g := by


  show moduleIHomEquiv (T₁ ⊗ X) m n
    ((actμ_ T₁ X m).hom ≫ (moduleIHomEquiv T₁ (X ⊗ᵐ m) n).symm (f ≫ g)) =
    f ▷ X ≫ moduleIHomEquiv (T₂ ⊗ X) m n
      ((actμ_ T₂ X m).hom ≫ (moduleIHomEquiv T₂ (X ⊗ᵐ m) n).symm g)

  rw [show (moduleIHomEquiv T₁ (X ⊗ᵐ m) n).symm (f ≫ g) =
    f ▷ᵐ (X ⊗ᵐ m) ≫ (moduleIHomEquiv T₂ (X ⊗ᵐ m) n).symm g from by
      rw [moduleIHomEquiv_symm_eq, actWhiskerRight_comp, assoc,
          ← moduleIHomEquiv_symm_eq]]

  have h_mu_nat : (actμ_ T₁ X m).hom ≫ f ▷ᵐ (X ⊗ᵐ m) =
    (f ▷ X) ▷ᵐ m ≫ (actμ_ T₂ X m).hom := by
    have := LeftModuleCategory.actAssociator_naturality (M := M) f (𝟙 X) (𝟙 m)
    simp [LeftModuleCategory.actTensorHom_def] at this
    exact this.symm

  conv_lhs => rw [show (actμ_ T₁ X m).hom ≫ f ▷ᵐ (X ⊗ᵐ m) ≫ (moduleIHomEquiv T₂ (X ⊗ᵐ m) n).symm g =
    (f ▷ X) ▷ᵐ m ≫ (actμ_ T₂ X m).hom ≫ (moduleIHomEquiv T₂ (X ⊗ᵐ m) n).symm g from by
      rw [← assoc, h_mu_nat, assoc]]

  rw [moduleIHomEquiv_natural]

/-- Naturality in `Y` of `moduleIHom_tensor_equiv`:
`tensor_equiv (f ≫ g) = f ≫ tensor_equiv g`. -/
theorem moduleIHom_tensor_equiv_natural {Y₁ Y₂ X : C} [HasRightDual X] {m n : M}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) :
    moduleIHom_tensor_equiv Y₁ X m n (f ≫ g) =
      f ≫ moduleIHom_tensor_equiv Y₂ X m n g := by
  simp only [moduleIHom_tensor_equiv, Equiv.trans_apply]
  rw [moduleIHom_curry_equiv_symm_natural]


  apply (tensorRightHomEquiv Y₁ X Xᘁ (moduleIHom m n)).symm.injective
  rw [Equiv.symm_apply_apply, tensorRightHomEquiv_symm_naturality]
  congr 1
  exact ((tensorRightHomEquiv Y₂ X Xᘁ (moduleIHom m n)).symm_apply_apply _).symm

end CategoryTheory
