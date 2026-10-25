/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi
import Structure.v1.Atlas.TensorCategories.code.GroupoidMultitensor.Part3
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


namespace GroupoidMultitensor

attribute [instance] FiniteGroupoidData.finObj FiniteGroupoidData.finMor

attribute [instance] FiniteGroupoidData.decEqObj FiniteGroupoidData.decEqMor

attribute [instance] GroupoidGradedVecData.instAddCommMonoid GroupoidGradedVecData.instModule

attribute [instance] MatrixVecData.instAddCommMonoid MatrixVecData.instModule

/-- Category structure on `MatrixVecData k n`: morphisms are entrywise linear maps. -/
@[reducible]
def matVecCategoryInstance (k : Type w) [Field k] (n : ℕ) :
    Category.{w} (MatrixVecData k n) where
  Hom V W := ∀ i j, V.component i j →ₗ[k] W.component i j
  id V i j := LinearMap.id
  comp f g i j := (g i j).comp (f i j)
  id_comp f := by funext i j; simp [LinearMap.comp_id]
  comp_id f := by funext i j; simp [LinearMap.id_comp]
  assoc f g h := by funext i j; rfl

end GroupoidMultitensor
