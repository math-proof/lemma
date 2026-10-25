/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean -/

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
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Projective
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.RegularObject
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
import Abbrev.v1.Atlas.TensorCategories.code.RegularObject.Part2
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part7
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
