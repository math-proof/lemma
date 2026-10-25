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
import Def.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part6
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

/-- The FP-dimension of the regular object is the sum
`∑_i (regularCoeff_i) · (FPdim of projective cover_i)`. -/
theorem HasRegularObject.fpdimRegular_eq {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] :
    HasRegularObject.fpdimRegular (C := C) =
      ∑ i : h.ι, h.regularCoeff i * h.fpDimProjCover i := by
  unfold fpdimRegular FormalProjectiveSum.fpdim regularCoeff fpDimProjCover
  rfl

/-- The FP-dimension of the regular object is strictly positive. -/
theorem HasRegularObject.fpdimRegular_pos {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [h : HasRegularObject C] :
    HasRegularObject.fpdimRegular (C := C) > 0 := by
  rw [fpdimRegular_eq]
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (h.regularCoeff_pos i) (h.fpDimProjCover_pos i)
  · exact Finset.univ_nonempty

end SimpleLemmas
end FiniteTensorCategoryLemmas
end CategoryTheory
