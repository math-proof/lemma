/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.GroupTheory.QuotientGroup.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme.Part2
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace CartierDivisorScheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The principal Cartier divisor associated to a rational function `g ∈ K(X)ˣ`, given by the
single-chart cover `{⊤}` with `f = g`. -/
noncomputable def CartierDivisorDatum.principal (g : (X.functionField)ˣ) :
    CartierDivisorDatum X where
  ι := PUnit
  cover := fun _ => ⊤
  cover_eq_top := by simp
  f := fun _ => g
  compat := fun _ _ h => by
    simp only [MonoidHom.mem_range]
    exact ⟨1, by simp [structureUnitsToFunctionFieldUnits]⟩

/-- The trivial Cartier divisor datum on `X`, corresponding to the principal divisor of `1`. -/
noncomputable def CartierDivisorDatum.trivialDatum : CartierDivisorDatum X :=
  CartierDivisorDatum.principal X 1

/-- Convert a rational function `g ∈ K(X)ˣ` into the associated principal Cartier divisor datum
on `X`. -/
noncomputable def toDatum (g : (X.functionField)ˣ) : CartierDivisorDatum X :=
  CartierDivisorDatum.principal X g

end CartierDivisorScheme
