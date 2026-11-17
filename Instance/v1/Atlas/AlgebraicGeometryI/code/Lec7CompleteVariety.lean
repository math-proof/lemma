/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7CompleteVariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Class.v1.Atlas.AlgebraicGeometryI.code.Lec7CompleteVariety

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u


namespace Formalization.Lec7CompleteVariety

/-- A proper morphism is a complete variety. -/
instance isCompleteVariety_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] : IsCompleteVariety f where
  isSeparated := inferInstance
  universallyClosed := inferInstance

end Formalization.Lec7CompleteVariety
