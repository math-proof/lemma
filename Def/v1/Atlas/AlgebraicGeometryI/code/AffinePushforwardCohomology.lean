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
open AlgebraicGeometry CategoryTheory Limits


noncomputable section

universe u

/-- The global sections functor `Γ(X, -) : X.Modules ⥤ Ab` sending a sheaf of `O_X`-modules to
its abelian group of global sections. -/
def Scheme.Modules.globalSectionsFunctor (X : Scheme.{u}) :
    X.Modules ⥤ Ab where
  obj F := Γ(F, ⊤)
  map φ := Scheme.Modules.Hom.app φ ⊤
  map_id _ := rfl
  map_comp _ _ := rfl

end
