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
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part2
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w


namespace TensorCategories

/-- A fiber functor on `C` is in particular a tensor functor from `C` to the
category of `k`-modules. -/
def FiberFunctor.toTensorFunctor
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (FF : FiberFunctor k C) : TensorFunctor k C (ModuleCat.{w} k) where
  F := FF.F
  faithful := FF.faithful
  preservesMono := FF.preservesMono
  preservesEpi := FF.preservesEpi
  monoidal := FF.monoidal

/-- A fiber functor is in particular a quasi-fiber functor, via its monoidal structure. -/
def FiberFunctor.toQuasiFiberFunctor
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (FF : FiberFunctor k C) : QuasiFiberFunctor k C :=
  ⟨FF.toTensorFunctor.toQuasiTensorFunctor⟩

/-- A tensor functor from `C` to the category of `k`-modules is a fiber functor on `C`. -/
def FiberFunctor.ofTensorFunctorToVec
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (TF : TensorFunctor k C (ModuleCat.{w} k)) :
    FiberFunctor k C where
  F := TF.F
  faithful := TF.faithful
  preservesMono := TF.preservesMono
  preservesEpi := TF.preservesEpi
  monoidal := TF.monoidal

/-- Exhibit a quasi-fiber functor as a quasi-tensor functor into the category of
`k`-modules. -/
def QuasiFiberFunctor.toQuasiTensorFunctorToVec
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (QFF : QuasiFiberFunctor k C) : QuasiTensorFunctor k C (ModuleCat.{w} k) :=
  QFF.toQuasiTensorFunctor

/-- Definition 1.34.1 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-fiber functor `QFF`
is normalized when the natural isomorphisms `J` are compatible with the left and
right unit constraints via the unit isomorphism. -/
def QuasiFiberFunctor.IsNormalized
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (QFF : QuasiFiberFunctor k C) : Prop :=
  (∀ X : C,
    (QFF.J (𝟙_ C) X).hom ≫ QFF.F.map (λ_ X).hom =
      (QFF.unitIso.hom ▷ QFF.F.obj X) ≫ (λ_ (QFF.F.obj X)).hom) ∧
  (∀ X : C,
    (QFF.J X (𝟙_ C)).hom ≫ QFF.F.map (ρ_ X).hom =
      (QFF.F.obj X ◁ QFF.unitIso.hom) ≫ (ρ_ (QFF.F.obj X)).hom)

end TensorCategories
