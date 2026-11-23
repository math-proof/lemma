/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AlgebraicEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Connected.Basic
public import Instance.v1.Atlas.AlgebraicGeometryI.code.AlgebraicEquivalence

@[expose] public section

noncomputable section

namespace AlgebraicEquivalence

open AlgebraicGeometry CategoryTheory Limits

universe u


namespace CartierDivisorGroup

/-- Pullback of (model) Cartier divisors along a morphism `f : X → Y`: compose with the
underlying continuous map. -/
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CartierDivisorGroup Y →+ CartierDivisorGroup X where
  toFun D := D ∘ f.base
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Placeholder predicate: a (model) divisor is principal. Always `True` in this skeleton. -/
def isPrincipal {X : Scheme.{u}} (_D : CartierDivisorGroup X) : Prop :=
  True


end CartierDivisorGroup
end AlgebraicEquivalence
end
