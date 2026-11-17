/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffinePushforwardHigher.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits


noncomputable section

universe u

namespace AffinePushforwardHigher

/-- Global sections functor `Γ(X, -) : X.Modules ⥤ Ab` for a scheme `X`. -/
def globalSectionsFunctor (X : Scheme.{u}) : X.Modules ⥤ Ab where
  obj F := Γ(F, ⊤)
  map φ := Scheme.Modules.Hom.app φ ⊤
  map_id _ := rfl
  map_comp _ _ := rfl

end AffinePushforwardHigher
end
