/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme.Part2

@[expose] public section

set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace CartierDivisorScheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The Cartier divisor group of `X` is inhabited by the trivial datum. -/
noncomputable instance instInhabitedCartierDivisorGroupScheme :
    Inhabited (CartierDivisorGroupScheme X) :=
  ⟨⟨PUnit, fun _ => ⊤, by simp, fun _ => 1, fun _ _ h => by
    simp only [MonoidHom.mem_range]
    exact ⟨1, by simp [structureUnitsToFunctionFieldUnits]⟩⟩⟩

end CartierDivisorScheme
