/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffinePushforwardHigher.lean -/

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
import Def.v1.Atlas.AlgebraicGeometryI.code.AffinePushforwardHigher
open AlgebraicGeometry CategoryTheory Limits


noncomputable section

universe u

namespace AffinePushforwardHigher

/-- The global sections functor is additive. -/
instance globalSectionsFunctor_additive (X : Scheme.{u}) :
    (globalSectionsFunctor X).Additive where
  map_add := fun {_ _ _ _} => rfl

end AffinePushforwardHigher
end
