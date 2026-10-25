/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessDefinition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.SeparatednessDefinition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u


namespace SeparatednessDefinition

variable (k : Type u) [Field k]

/-- The diagonal morphism `Δ : X → X ×_{Spec k} X` of a `k`-variety. -/
noncomputable def diagonalMorphism {X : Scheme.{u}} (f : X ⟶ SpecK k) :
    X ⟶ pullback f f :=
  pullback.diagonal f

end SeparatednessDefinition
