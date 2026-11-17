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
public import Def.v1.Atlas.AlgebraicGeometryI.code.AlgebraicEquivalence

@[expose] public section

noncomputable section

namespace AlgebraicEquivalence

open AlgebraicGeometry CategoryTheory Limits

universe u


namespace CartierDivisorGroup

/-- Abelian group structure on `CartierDivisorGroup`, pointwise. -/
instance instAddCommGroup (X : Scheme.{u}) : AddCommGroup (CartierDivisorGroup X) :=
  Pi.addCommGroup

end CartierDivisorGroup
end AlgebraicEquivalence
end
