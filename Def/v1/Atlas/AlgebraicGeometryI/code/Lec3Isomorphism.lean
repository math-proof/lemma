/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Isomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
open CategoryTheory AlgebraicGeometry


namespace AlgebraicGeometry

/-- A morphism of schemes is an *isomorphism* (Lecture 3) if it has a two-sided inverse. -/
def IsIsomorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y

end AlgebraicGeometry
