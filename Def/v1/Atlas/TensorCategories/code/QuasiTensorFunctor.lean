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
import Structure.v1.Atlas.TensorCategories.code.QuasiTensorFunctor
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w


namespace TensorCategories

/-- Every tensor functor is in particular a quasi-tensor functor: the monoidal
structure provides the natural isomorphisms `J` and the unit isomorphism. -/
def TensorFunctor.toQuasiTensorFunctor
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
    (TF : TensorFunctor k C D) : QuasiTensorFunctor k C D where
  F := TF.F
  faithful := TF.faithful
  preservesMono := TF.preservesMono
  preservesEpi := TF.preservesEpi
  J X Y := @Functor.Monoidal.μIso _ _ _ _ _ _ TF.F TF.monoidal X Y
  J_natural_left := by
    intro X X' f Y
    have := TF.monoidal
    simp [Functor.Monoidal.μIso, Functor.LaxMonoidal.μ_natural_left]
  J_natural_right := by
    intro X Y Y' g
    have := TF.monoidal
    simp [Functor.Monoidal.μIso, Functor.LaxMonoidal.μ_natural_right]
  unitIso := (@Functor.Monoidal.εIso _ _ _ _ _ _ TF.F TF.monoidal).symm

end TensorCategories
