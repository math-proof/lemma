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
import Class.v1.Atlas.TensorCategories.code.FPdimProps
set_option maxHeartbeats 800000


namespace CategoryTheory

open CategoryTheory MonoidalCategory Limits

attribute [reducible, instance] FiniteMultitensorDecompData.instFintype
  FiniteMultitensorDecompData.instDecEq

section Prop1472

variable {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    [d : FiniteMultitensorDecompData k C]

/-- Linear equivalence `(Z ⊗ P ⟶ Y) ≃ₗ[k] (P ⟶ (ᘁZ) ⊗ Y)` upgrading the
left-dual hom adjunction (`tensorLeftHomEquiv`) in a `k`-linear rigid
monoidal category. -/
noncomputable def tensorLeftHomLinearEquiv
    (Z P Y : C) :
    (Z ⊗ P ⟶ Y) ≃ₗ[k] (P ⟶ (ᘁZ) ⊗ Y) :=
  LinearEquiv.ofBijective
    { toFun := (tensorLeftHomEquiv P (ᘁZ) Z Y).toFun
      map_add' := fun f g => by
        simp only [tensorLeftHomEquiv]
        simp [MonoidalPreadditive.whiskerLeft_add]
      map_smul' := fun r f => by
        simp only [tensorLeftHomEquiv]
        simp [MonoidalLinear.whiskerLeft_smul] }
    ⟨fun f g h => (tensorLeftHomEquiv P (ᘁZ) Z Y).injective h,
     fun g => ⟨(tensorLeftHomEquiv P (ᘁZ) Z Y).symm g,
       (tensorLeftHomEquiv P (ᘁZ) Z Y).apply_symm_apply g⟩⟩

/-- Indexed family of projective covers whose biproduct decomposes
`P_i ⊗ Z`, with `k'`-summands repeated `Σ_l N_{k', i*}^l · [Z:X_l]` times
(the multiplicities appearing in Proposition 1.47.2, left version). -/
def projTensorLeftDecompFamily (i : d.I) (Z : C) :
    ((k' : d.I) × Fin (∑ l : d.I, d.structConst k' (d.dualIndex i) l * d.jhMult Z l)) → C :=
  fun p => d.projCover p.1

/-- Indexed family of projective covers whose biproduct decomposes
`Z ⊗ P_i`, with `k'`-summands repeated `Σ_l N_{l, k'}^i · [Z:X_l]` times
(the multiplicities appearing in Proposition 1.47.2, right version). -/
def projTensorRightDecompFamily (i : d.I) (Z : C) :
    ((k' : d.I) × Fin (∑ l : d.I, d.structConst l k' i * d.jhMult Z l)) → C :=
  fun p => d.projCover p.1

end Prop1472
end CategoryTheory
