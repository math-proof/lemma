/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffinePushforwardCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Category.Grp.Abelian
import Def.v1.Atlas.AlgebraicGeometryI.code.AffinePushforwardCohomology
open AlgebraicGeometry CategoryTheory Limits


noncomputable section

universe u

/-- `Γ(X, -)` is an additive functor. -/
instance Scheme.Modules.globalSectionsFunctor_additive
    (X : Scheme.{u}) : (Scheme.Modules.globalSectionsFunctor X).Additive where
  map_add := fun {_ _ _ _} => rfl

end
