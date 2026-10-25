/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Scheme


noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

/-- A morphism between varieties, defined here as a scheme morphism `X ⟶ Y`. -/
abbrev VarietyMorphism (X Y : Scheme.{u}) : Type u := X ⟶ Y

end
