/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Instance.v1.Atlas.TensorCategories.code.MonoidalFunctorProps
set_option maxHeartbeats 800000


namespace TensorCategories.MonoidalFunctorProps

open CategoryTheory MonoidalCategory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

section Exercise_1_10_15

open Category

/-- Candidate inverse of `α.app X` at a right-dualizable object `X`, built from the
evaluation/coevaluation of the right dual together with the inverse component `α.app Xᘁ`. -/
noncomputable def monoidalNatTrans_inv
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X : C) [HasRightDual X] : G.obj X ⟶ F.obj X :=
  (λ_ (G.obj X)).inv
  ≫ (ExactPairing.coevaluation (F.obj X) (F.obj Xᘁ) ▷ G.obj X)
  ≫ (α_ (F.obj X) (F.obj Xᘁ) (G.obj X)).hom
  ≫ (F.obj X ◁ (α.app Xᘁ ▷ G.obj X))
  ≫ (F.obj X ◁ ExactPairing.evaluation (G.obj X) (G.obj Xᘁ))
  ≫ (ρ_ (F.obj X)).hom

end Exercise_1_10_15
end TensorCategories.MonoidalFunctorProps
