/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Products.Basic
import Instance.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part4
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


section Thm_1_21_1

open MonoidalCategory

variable (k : Type u) [CommRing k]

variable (C : Type v) [Category.{w} C] [MonoidalCategory C] [Preadditive C] [Linear k C]

variable (F : C ⥤ ModuleCat.{u} k) [F.Monoidal] [F.Faithful]

set_option synthInstance.maxHeartbeats 400000

/-- Proposition 1.18.3: the canonical algebra isomorphism
`End(F₁) ⊗ End(F₂) ≅ End(F₁ ⊗ F₂)`, here specialized to `F₁ = F₂ = F`. -/
def evalAtHom (Z : C) : End F →ₗ[k] (↑(F.obj Z) →ₗ[k] ↑(F.obj Z)) where
  toFun η := (η.app Z).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Wrap a `k`-linear endomorphism of the underlying module into the corresponding
endomorphism in `ModuleCat k`. -/
def wrapEnd (M : ModuleCat.{u} k) : (↑M →ₗ[k] ↑M) →ₗ[k] End M where
  toFun f := ModuleCat.ofHom f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical map `End(F) ⊗ End(F) → End(F(X) ⊗ F(Y))` sending `η₁ ⊗ η₂` to
`η₁ ⊗ η₂` evaluated component-wise. -/
noncomputable def endF_tensor_hom (X Y : C) :
    (End F) ⊗[k] (End F) →ₗ[k] End (F.obj X ⊗ F.obj Y) :=
  (wrapEnd k (F.obj X ⊗ F.obj Y)) ∘ₗ
  (TensorProduct.homTensorHomMap (.id k) ↑(F.obj X) ↑(F.obj Y) ↑(F.obj X) ↑(F.obj Y)) ∘ₗ
  (TensorProduct.map (evalAtHom k C F X) (evalAtHom k C F Y))

/-- The coalgebra structure on `End(F)` arising from `endF_comul` and `endF_counit_def`. -/
def thm_1_21_1_converse (R' : Type*) (H' : Type*) [CommSemiring R'] [Semiring H']
    [Algebra R' H']
    (Δ : H' →ₐ[R'] H' ⊗[R'] H') (ε : H' →ₐ[R'] R')
    (h_coassoc : (Algebra.TensorProduct.assoc R' R' R' H' H' H').toAlgHom.comp
      ((Algebra.TensorProduct.map Δ (.id R' H')).comp Δ) =
      (Algebra.TensorProduct.map (.id R' H') Δ).comp Δ)
    (h_rTensor : (Algebra.TensorProduct.map ε (.id R' H')).comp Δ =
      (Algebra.TensorProduct.lid R' H').symm.toAlgHom)
    (h_lTensor : (Algebra.TensorProduct.map (.id R' H') ε).comp Δ =
      (Algebra.TensorProduct.rid R' R' H').symm.toAlgHom) :
    Bialgebra R' H' :=
  Bialgebra.ofAlgHom Δ ε h_coassoc h_rTensor h_lTensor

end Thm_1_21_1
