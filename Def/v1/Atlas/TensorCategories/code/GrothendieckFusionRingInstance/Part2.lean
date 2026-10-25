/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Theorem.v1.Atlas.TensorCategories.code.GrothendieckFusionRingInstance
open CategoryTheory MonoidalCategory Finset

universe v u


namespace CategoryTheory

section JHLift

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]
  [cfd : CategoricalFusionData κ C]
  [jh : HasJordanHolderMultiplicities κ C]

/-- Packages the lifted Jordan-Hölder Frobenius-Perron dimension as an `FPdimFunction` on `C`. -/
noncomputable def jhLiftFPdimData
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData) :
    FPdimFunction (C := C) where
  fpDim := jhFpDim fpd
  fpDim_unit := jhFpDim_unit fpd
  fpDim_pos := jhFpDim_pos fpd
  fpDim_tensor := jhFpDim_tensor fpd
  fpDim_iso := jhFpDim_iso fpd

end JHLift

/-- From `CategoricalFusionData` together with Jordan-Hölder multiplicities and the
Perron-Frobenius property, the category `C` carries a Grothendieck fusion ring. -/

section Rank1

/-- The trivial rank-one fusion ring with index set `Fin 1` and the single basis element
acting as the unit. -/
def rank1FusionRing : FusionRing (Fin 1) where
  unit := 0
  N := fun _ _ _ => 1
  star := id
  star_star := fun _ => rfl
  unit_mul := fun j k => by
    have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
    have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
    subst hj; subst hk; simp
  mul_unit := fun i k => by
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
    subst hi; subst hk; simp
  duality := fun i j => by
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
    subst hi; subst hj; simp
  assoc := fun _ _ _ _ => by simp
  N_star_transpose := fun _ _ _ => rfl

end Rank1
end CategoryTheory
