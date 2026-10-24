/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4AffineMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Affine

open AlgebraicGeometry CategoryTheory

universe u

/-- Lecture 4, Definition 9: an *affine morphism* `f : X → Y` of schemes is one for which there
exists an affine open cover of `Y` whose preimages in `X` are affine. -/
abbrev IsAffineMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsAffineHom f
