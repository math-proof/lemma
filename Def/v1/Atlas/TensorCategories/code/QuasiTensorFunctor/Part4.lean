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
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part3

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w


namespace TensorCategories

/-- Definition 1.34.2 (Etingof–Gelaki–Nikshych–Ostrik): Two quasi-fiber functors
on `C` are twist-equivalent if they share the same underlying functor. -/
def QuasiFiberFunctor.TwistEquivalent
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (QFF₁ QFF₂ : QuasiFiberFunctor k C) : Prop :=
  QFF₁.F = QFF₂.F

/-- The twist isomorphism on `QFF₁.F X ⊗ QFF₁.F Y` obtained from a twist-equivalence
`h : QFF₁.TwistEquivalent QFF₂`, comparing the two natural isomorphisms `J` on
the same underlying functor. -/
noncomputable def QuasiFiberFunctor.twist
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (QFF₁ QFF₂ : QuasiFiberFunctor k C)
    (h : QFF₁.TwistEquivalent QFF₂) (X Y : C) :
    QFF₁.F.obj X ⊗ QFF₁.F.obj Y ≅ QFF₁.F.obj X ⊗ QFF₁.F.obj Y := by
  have hobj : ∀ Z : C, QFF₁.F.obj Z = QFF₂.F.obj Z := fun Z => by rw [h]


  exact eqToIso (by simp [hobj]) ≪≫ QFF₂.J X Y ≪≫ eqToIso (by simp [hobj]) ≪≫
    (QFF₁.J X Y).symm

end TensorCategories
