/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w


namespace TensorCategories

section QuasiTensorExactness

variable {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]

/-- A quasi-tensor functor preserves the unit object, as recorded by its unit isomorphism. -/
def QuasiTensorFunctor.preservesUnit
    (QTF : QuasiTensorFunctor k C D) : QTF.F.obj (𝟙_ C) ≅ 𝟙_ D :=
  QTF.unitIso

end QuasiTensorExactness

section TensorFunctorProps

variable {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]

/-- The unit isomorphism of a tensor functor, derived from its monoidal structure. -/
def TensorFunctor.preservesUnit
    (TF : TensorFunctor k C D) : TF.F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (@Functor.Monoidal.εIso _ _ _ _ _ _ TF.F TF.monoidal).symm

/-- A quasi-tensor functor whose underlying functor carries a monoidal structure
upgrades to a tensor functor. -/
def QuasiTensorFunctor.toTensorFunctor_of_monoidal
    (QTF : QuasiTensorFunctor k C D)
    (hmon : QTF.F.Monoidal) : TensorFunctor k C D where
  F := QTF.F
  faithful := QTF.faithful
  preservesMono := QTF.preservesMono
  preservesEpi := QTF.preservesEpi
  monoidal := hmon

end TensorFunctorProps
end TensorCategories
