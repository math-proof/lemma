/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Def.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part2
public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w


namespace TensorCategories

/-- Definition 1.19.1 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-fiber functor on an
abelian monoidal category `C` over a field `k` is a quasi-tensor functor from `C`
to the category of `k`-modules. -/
structure QuasiFiberFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    extends QuasiTensorFunctor k C (ModuleCat.{w} k)

/-- Definition 1.19.1 (Etingof–Gelaki–Nikshych–Ostrik): A fiber functor on an
abelian monoidal category `C` over a field `k` is a tensor functor from `C` to the
category of `k`-modules. -/
structure FiberFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] where
  F : C ⥤ ModuleCat.{w} k
  faithful : F.Faithful
  preservesMono : F.PreservesMonomorphisms
  preservesEpi : F.PreservesEpimorphisms
  monoidal : F.Monoidal

end TensorCategories
