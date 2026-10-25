/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorProps
set_option maxHeartbeats 800000


namespace TensorCategories.MonoidalFunctorProps

open CategoryTheory MonoidalCategory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

section Exercise_1_10_15

open Category

/-- Compatibility of a monoidal natural transformation with the evaluation of an exact
pairing transported through `F` and `G`. -/
lemma monoidalNatTrans_tensorHom_comp_eval
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X Y : C) [ExactPairing X Y] :
    (α.app Y ⊗ₘ α.app X) ≫
      @ExactPairing.evaluation D _ _ (G.obj X) (G.obj Y) (monoidalFunctor_exactPairing G X Y) =
      @ExactPairing.evaluation D _ _ (F.obj X) (F.obj Y) (monoidalFunctor_exactPairing F X Y) := by

  show (α.app Y ⊗ₘ α.app X) ≫
    ((Monoidal.μIso G Y X).hom ≫ G.map (ExactPairing.evaluation X Y) ≫ (Monoidal.εIso G).inv) =
    (Monoidal.μIso F Y X).hom ≫ F.map (ExactPairing.evaluation X Y) ≫ (Monoidal.εIso F).inv
  simp only [Monoidal.μIso_hom, Monoidal.εIso_inv]

  rw [← NatTrans.IsMonoidal.tensor_assoc (τ := α) Y X]
  congr 1

  rw [← α.naturality_assoc (ε_ X Y)]
  congr 1

  rw [← cancel_epi (LaxMonoidal.ε F)]
  rw [NatTrans.IsMonoidal.unit_assoc (τ := α)]
  simp

/-- Compatibility of a monoidal natural transformation with the coevaluation of an exact
pairing transported through `F` and `G`. -/
lemma monoidalNatTrans_coev_comp_tensorHom
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X Y : C) [ExactPairing X Y] :
    @ExactPairing.coevaluation D _ _ (F.obj X) (F.obj Y) (monoidalFunctor_exactPairing F X Y) ≫
      (α.app X ⊗ₘ α.app Y) =
      @ExactPairing.coevaluation D _ _ (G.obj X) (G.obj Y) (monoidalFunctor_exactPairing G X Y) := by

  show ((Monoidal.εIso F).hom ≫ F.map (ExactPairing.coevaluation X Y) ≫ (Monoidal.μIso F X Y).inv) ≫
      (α.app X ⊗ₘ α.app Y) =
    (Monoidal.εIso G).hom ≫ G.map (ExactPairing.coevaluation X Y) ≫ (Monoidal.μIso G X Y).inv
  simp only [Monoidal.εIso_hom, Monoidal.μIso_inv, assoc]

  rw [← cancel_mono (LaxMonoidal.μ G X Y)]
  simp only [assoc]
  rw [Monoidal.δ_μ, comp_id]
  rw [← NatTrans.IsMonoidal.tensor (τ := α) X Y]
  rw [Monoidal.δ_μ_assoc]

  slice_lhs 2 3 => rw [α.naturality]

  rw [reassoc_of% (NatTrans.IsMonoidal.unit (τ := α))]

end Exercise_1_10_15
end TensorCategories.MonoidalFunctorProps
