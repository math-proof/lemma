/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessDefinition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SeparatednessDefinition

variable (k : Type u) [Field k]

/-- The base scheme `Spec k` for varieties over a field `k`. -/
noncomputable abbrev SpecK : Scheme.{u} := Spec (CommRingCat.of k)

/-- A `k`-variety `X` (with structure morphism `f : X → Spec k`) is
*separated* when `f` is a separated morphism. -/
abbrev IsSeparatedVariety {X : Scheme.{u}} (f : X ⟶ SpecK k) : Prop :=
  IsSeparated f

/-- The diagonal morphism `Δ : X → X ×_{Spec k} X` of a `k`-variety. -/
noncomputable def diagonalMorphism {X : Scheme.{u}} (f : X ⟶ SpecK k) :
    X ⟶ pullback f f :=
  pullback.diagonal f
