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
public import Def.v1.Atlas.AlgebraicGeometryI.code.AlgebraicEquivalence.Part2


public noncomputable section

namespace AlgebraicEquivalence

open AlgebraicGeometry CategoryTheory Limits

universe u


namespace CartierDivisorGroup

/-- An `S`-point of a scheme `X` over `S`: a section of the structure morphism `p : X → S`. -/
structure SPoint {S X : Scheme.{u}} (p : X ⟶ S) where
  morphism : S ⟶ X
  isSection : morphism ≫ p = 𝟙 S

/-- A connected variety over `S`: an integral, topologically connected scheme equipped with a
structure morphism to `S`. Used to parametrize algebraic families. -/
structure ConnectedVariety (S : Scheme.{u}) where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ S
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  isConnected : ConnectedSpace toScheme


end CartierDivisorGroup
end AlgebraicEquivalence
end
