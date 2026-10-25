/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
set_option maxHeartbeats 800000


namespace CategoryTheory

open CategoryTheory MonoidalCategory Limits

/-- Linear equivalence `(X ⊗ Z ⟶ Y) ≃ₗ[k] (X ⟶ Y ⊗ Zᘁ)` upgrading the
right-dual hom adjunction (`tensorRightHomEquiv`) in a `k`-linear rigid
monoidal category. -/
noncomputable def tensorRightHomLinearEquiv (k : Type w) [Field k]
    {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear k C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    (X Z Y : C) :
    (X ⊗ Z ⟶ Y) ≃ₗ[k] (X ⟶ Y ⊗ Zᘁ) :=
  LinearEquiv.ofBijective
    { toFun := (tensorRightHomEquiv X Z (Zᘁ) Y).toFun
      map_add' := fun f g => by
        simp only [tensorRightHomEquiv]
        simp [MonoidalPreadditive.add_whiskerRight]
      map_smul' := fun r f => by
        simp only [tensorRightHomEquiv]
        simp [MonoidalLinear.smul_whiskerRight] }
    ⟨fun f g h => (tensorRightHomEquiv X Z (Zᘁ) Y).injective h,
     fun g => ⟨(tensorRightHomEquiv X Z (Zᘁ) Y).symm g,
       (tensorRightHomEquiv X Z (Zᘁ) Y).apply_symm_apply g⟩⟩

end CategoryTheory
