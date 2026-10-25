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
import Structure.v1.Atlas.TensorCategories.code.GroupoidMultitensor.Part2
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


namespace GroupoidMultitensor

attribute [instance] FiniteGroupoidData.finObj FiniteGroupoidData.finMor

attribute [instance] FiniteGroupoidData.decEqObj FiniteGroupoidData.decEqMor

attribute [instance] GroupoidGradedVecData.instAddCommMonoid GroupoidGradedVecData.instModule

/-- A morphism `g` is a unit-component iff it equals some identity morphism `G.id x`. -/
def GroupoidGradedVecData.isUnitComponent (G : FiniteGroupoidData) (g : G.Mor) : Prop :=
  ∃ x : G.Obj, g = G.id x

/-- Grading shift for the dual object: invert the morphism. -/
def GroupoidGradedVecData.dualGrading (G : FiniteGroupoidData) (g : G.Mor) : G.Mor :=
  G.inv g

/-- Category structure on `GroupoidGradedVecData k G`: a morphism is a family of `k`-linear
maps between the components indexed by morphisms of `G`. -/
@[reducible]
def ggvCategoryInstance (k : Type w) [Field k] (G : FiniteGroupoidData.{u, v}) :
    Category.{max v w} (GroupoidGradedVecData k G) where
  Hom V W := ∀ g : G.Mor, V.component g →ₗ[k] W.component g
  id V g := LinearMap.id
  comp f g h := (g h).comp (f h)
  id_comp f := by funext g; simp [LinearMap.comp_id]
  comp_id f := by funext g; simp [LinearMap.id_comp]
  assoc f g h := by funext i; rfl

end GroupoidMultitensor
