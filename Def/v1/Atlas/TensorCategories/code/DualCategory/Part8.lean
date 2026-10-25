/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Instance.v1.Atlas.TensorCategories.code.DualCategory.Part4
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

namespace DualCatObj

variable {C M}

attribute [reassoc] Hom.comm

/-- Construct an inverse morphism `𝟙 ⟶ F` from a morphism `α : F ⟶ 𝟙` whose components
are isomorphisms at every object of `M`. -/
noncomputable def Hom.mkInverse
    {F : DualCatObj C M}
    (α : Hom F (idModuleFunctor (C := C) (M := M)))
    (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
    Hom (idModuleFunctor (C := C) (M := M)) F where
  natTrans := {
    app := fun N => @inv _ _ _ _ (α.natTrans.app N) (hiso N)
    naturality := fun {N₁ N₂} f => by
      haveI := hiso N₁
      haveI := hiso N₂
      have hnat := α.natTrans.naturality f
      rw [← cancel_epi (α.natTrans.app N₁)]
      simp only [assoc, IsIso.hom_inv_id_assoc]
      rw [← assoc]
      rw [← hnat]
      simp [IsIso.hom_inv_id]

  }
  comm := fun X N => by
    haveI := hiso N
    haveI := hiso (X ⊗ᵐ N)
    have hcomm := α.comm X N
    show inv (α.natTrans.app (X ⊗ᵐ N)) ≫ (F.strIso X N).hom =
      (idModuleFunctor.strIso X N).hom ≫ X ◁ᵐ inv (α.natTrans.app N)
    rw [IsIso.inv_comp_eq]
    rw [← assoc, ← hcomm.symm, assoc, ← actWhiskerLeft_comp, IsIso.hom_inv_id,
        LeftModuleCategory.actWhiskerLeft_id, comp_id]

/-- If `M` is an indecomposable module category, then the monoidal unit of the dual
category `C*_M` is a simple object. -/
def actionFunctor (X : C) : M ⥤ M where
  obj := fun N => X ⊗ᵐ N
  map := fun f => X ◁ᵐ f
  map_id := fun N => by simp [LeftModuleCategory.actWhiskerLeft_id]
  map_comp := fun f g => by
    have h1 := LeftModuleCategory.actTensorHom_comp (𝟙 X) f (𝟙 X) g
    simp [LeftModuleCategory.actTensorHom_def,
          LeftModuleCategory.actId_whiskerRight] at h1
    exact h1.symm

/-- If `M` is an exact module category over `C`, the canonical evaluation action turns
`M` into a left module category over the dual category `C*_M`. -/
def DoubleDualObj (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [LeftModuleCategory (DualCatObj C M) M] :=
  ModuleFunctor (DualCatObj C M) M M

end DualCatObj
end CategoryTheory
