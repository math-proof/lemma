/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffinePushforwardCohomology.lean -/

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
public import Def.v1.Atlas.AlgebraicGeometryI.code.AffinePushforwardCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits


noncomputable section

universe u

/-- `Γ(X, -)` is an additive functor. -/
instance Scheme.Modules.globalSectionsFunctor_additive
    (X : Scheme.{u}) : (Scheme.Modules.globalSectionsFunctor X).Additive where
  map_add := fun {_ _ _ _} => rfl

end
