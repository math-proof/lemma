/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8CompleteVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Class.v1.Atlas.AlgebraicGeometryI.code.Lec8CompleteVarieties

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u


namespace Formalization.Lec8CompleteVarieties

/-- A proper morphism is complete. -/
instance isComplete_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsComplete f where
  isSeparated := inferInstance
  universallyClosed := inferInstance

end Formalization.Lec8CompleteVarieties
