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
import Class.v1.Atlas.TensorCategories.code.CategoricalFreeness
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w


namespace CategoryTheory

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

end CategoryTheory
