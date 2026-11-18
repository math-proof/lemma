/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Projective
public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
public import Theorem.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
public import Theorem.Category.Atlas.v1.TensorCategories.code.RegularObject
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
public import Abbrev.v1.Atlas.TensorCategories.code.RegularObject.Part2
public import Structure.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part2
public import Def.v1.Atlas.TensorCategories.code.FiniteTensorCategory

@[expose] public section
set_option maxHeartbeats 800000


universe w₀

open scoped TensorProduct


namespace CategoryTheory

section FiniteTensorCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteTensorCategory k C]

section SimpleLemmas

variable {C : Type u} [Category.{v} C]

attribute [instance] FiniteTensorCategoryData.ι_fintype
  FiniteTensorCategoryData.ι_decidableEq FiniteTensorCategoryData.ι_nonempty

namespace FiniteTensorCategoryData

variable (D : FiniteTensorCategoryData)

/-- Each Frobenius-Perron dimension of a simple object is an algebraic integer. -/
def regularObjectCoeff (i : D.ι) : ℝ := D.fpDimSimple i

/-- The Frobenius-Perron dimension of the category, given by
`∑_i FPdim(X_i) · FPdim(P_{X_i})`. -/
noncomputable def catFPdim : ℝ :=
  ∑ i : D.ι, D.fpDimSimple i * D.fpDimProjCover i

/-- Each FP-dimension of a projective cover is an algebraic integer, deduced from the
Cartan-matrix expansion. -/
def keyEquation_prop : Prop :=
  ∀ (mult : D.ι → ℕ), ∀ (fpDimZ : ℝ),
    (fpDimZ = ∑ j : D.ι, (mult j : ℝ) * D.fpDimSimple j) →
    (∑ i : D.ι, D.fpDimSimple i * (mult i : ℝ)) = fpDimZ

end FiniteTensorCategoryData
end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
