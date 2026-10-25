/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/EndTensorProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Def.v1.Atlas.TensorCategories.code.EndTensorProduct
set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory MonoidalCategory

namespace EndTensorProduct

universe u

variable (k : Type u) [Field k]

/-- Semiring structure on the tensor product `End(F₁) ⊗[k] End(F₂)` coming from the
`k`-algebra tensor product. -/
instance endFunctorTensorSemiring
    {C₁ : Type u} [Category.{u} C₁]
    {C₂ : Type u} [Category.{u} C₂]
    (F₁ : C₁ ⥤ FGModuleCat.{u} k) (F₂ : C₂ ⥤ FGModuleCat.{u} k) :
    Semiring (TensorProduct k (End F₁) (End F₂)) :=
  Algebra.TensorProduct.instSemiring

/-- `k`-algebra structure on the tensor product `End(F₁) ⊗[k] End(F₂)`. -/
instance endFunctorTensorAlgebra
    {C₁ : Type u} [Category.{u} C₁]
    {C₂ : Type u} [Category.{u} C₂]
    (F₁ : C₁ ⥤ FGModuleCat.{u} k) (F₂ : C₂ ⥤ FGModuleCat.{u} k) :
    Algebra k (TensorProduct k (End F₁) (End F₂)) :=
  Algebra.TensorProduct.instAlgebra

end EndTensorProduct
end
