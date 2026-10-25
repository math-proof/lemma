/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCatEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Class.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]


attribute [instance] InternalEndAlgebra.monObj

variable {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]

/-- If the internal-Hom functor `F` is exact and the chosen generator generates `M`,
then `F` is faithful. -/
noncomputable def internalHomEquivalence_of_steps
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M]
    [hFaith : InternalHomFaithful C M]
    [hFull : InternalHomFull C M]
    [hEss : InternalHomEssSurj C M] :
    M ≌ RightMod_ (A := hom.endAlgebra.carrier) := by
  haveI := hFaith.faithful
  haveI := hFull.full
  haveI := hEss.essSurj
  haveI : hom.F.IsEquivalence := { faithful := ‹_›, full := ‹_›, essSurj := ‹_› }
  exact hom.F.asEquivalence

end CategoryTheory
