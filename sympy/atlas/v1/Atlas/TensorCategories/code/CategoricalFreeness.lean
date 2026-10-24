/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CategoricalFreeness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w

namespace CategoryTheory

/-- A surjective quasi-tensor functor between abelian monoidal categories: here packaged as
the underlying functor `F : C ⥤ D`. Used as a stand-in for the data of a quasi-tensor
functor along with the surjectivity hypothesis of Definition 1.49.1. -/
structure SurjectiveQuasiTensorFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D

/-- A Frobenius-Perron dimension function `fpDim : C → ℝ` on a monoidal category,
normalized so that `fpDim (𝟙_ C) = 1`, taking positive values, multiplicative on tensor
products and invariant under isomorphisms. -/
structure FPdimFunction {C : Type u} [Category.{v} C] [MonoidalCategory C] where
  fpDim : C → ℝ
  fpDim_unit : fpDim (𝟙_ C) = 1
  fpDim_pos : ∀ (X : C), fpDim X > 0
  fpDim_tensor : ∀ (X Y : C), fpDim (X ⊗ Y) = fpDim X * fpDim Y
  fpDim_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → fpDim X = fpDim Y

namespace FPdimFunction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A Frobenius-Perron dimension function is integral (Definition 1.48.1) if the dimension
of every object is an integer. -/
def IsIntegral (d : FPdimFunction (C := C)) : Prop :=
  ∀ (X : C), ∃ (n : ℤ), d.fpDim X = ↑n

end FPdimFunction

/-- Combinatorial data describing the simple/projective decomposition of a finite
multitensor category: a finite indexing type `I`, simple objects `simpleObj i`, projective
covers `projCover i`, multiplicities of `projCover` in arbitrary objects, and the
distinguished index for the unit object. -/
class FiniteMultitensorDecompData (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] where
  I : Type*
  [instFintype : Fintype I]
  [instDecEq : DecidableEq I]
  simpleObj : I → C
  projCover : I → C
  projDecompMult : C → I → ℕ
  unitIdx : I
  simpleObj_unitIdx : Nonempty (simpleObj unitIdx ≅ 𝟙_ C)

attribute [reducible, instance] FiniteMultitensorDecompData.instFintype
  FiniteMultitensorDecompData.instDecEq

/-- The Frobenius-Perron dimension `FPdim(C)` of a finite tensor category
(Definition 1.47.5): `Σ FPdim(X_i) FPdim(P_i)` summed over simple objects `X_i` and their
projective covers `P_i`. -/
noncomputable def categoricalFPdim
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    (decomp : FiniteMultitensorDecompData k C)
    (d : FPdimFunction (C := C)) : ℝ :=
  ∑ i : decomp.I, d.fpDim (decomp.simpleObj i) * d.fpDim (decomp.projCover i)

/-- The coefficient `[F(R_C) : X_j]` of the simple object `X_j` of `D` in the image of the
regular object `R_C` under the functor `F`, expressed via the simple/projective
decomposition data of `C`. -/
noncomputable def coeffF_RC
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (j : decompD.I) : ℝ :=
  ∑ i : decompC.I,
    dC.fpDim (decompC.simpleObj i) *
      (decompD.projDecompMult (QTF.F.obj (decompC.projCover i)) j : ℝ)

/-- Theorem 1.50.1: For a surjective quasi-tensor functor `F : C → D`, the image of the
regular object is `F(R_C) = (FPdim(C)/FPdim(D)) R_D`, expressed coefficient-wise on simple
objects. -/
noncomputable def homDimSum
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (dC : FPdimFunction (C := C)) : ℝ :=
  ∑ i : decompC.I,
    dC.fpDim (decompC.simpleObj i) *
      (Module.finrank k (QTF.F.obj (decompC.projCover i) ⟶ 𝟙_ D) : ℝ)

/-- Corollary 1.50.2 (formula part): `FPdim(C)/FPdim(D) = Σ FPdim(X_i) dim Hom(F(P_i),
𝟙_D)`. -/
end CategoryTheory
