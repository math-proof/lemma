/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic

@[expose] public section

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
