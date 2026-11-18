module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
public import Abbrev.v1.Atlas.TensorCategories.code.RegularObject.Part2
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part7
public section
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

/-- Hypothesis package giving the inequality
`fpdimCat C > numSimples · fpdimProjUnit` together with positivity of the witnesses. -/
class HasFPdimInequality (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [EnoughProjectives C]
    [HasCategoricalFPdim C] where
  numSimples : ℕ
  numSimples_pos : numSimples > 0
  fpdimProjUnit : ℝ
  fpdimProjUnit_pos : fpdimProjUnit > 0
  fpdim_gt_numSimples_mul_fpdimProjUnit :
    HasCategoricalFPdim.fpdimCat (C := C) > ↑numSimples * fpdimProjUnit

section FPdimInequalityLemmas

variable {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [EnoughProjectives C]
    [HasCategoricalFPdim C] [h : HasFPdimInequality C]

/-- Witnesses that the categorical FP-dimension equals the dimension of an associated
finite-dimensional algebra. -/
class HasFPdimEqDimAlgebra (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasCategoricalFPdim C] where
  dimAlgebra : ℕ
  fpdimCat_eq_dimAlgebra : HasCategoricalFPdim.fpdimCat (C := C) = ↑dimAlgebra

/-- A Cartan matrix structure on a `k`-linear category with Jordan-Hölder multiplicities:
a finite index set `ι` and integer entries with positive diagonal. -/
class HasCartanMatrix (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [HasJordanHolderMultiplicity k C] where
  ι : Type*
  [ι_fintype : Fintype ι]
  cartanEntry : ι → ι → ℕ
  cartanEntry_diag_pos : ∀ (i : ι), cartanEntry i i ≥ 1

end FPdimInequalityLemmas
end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
