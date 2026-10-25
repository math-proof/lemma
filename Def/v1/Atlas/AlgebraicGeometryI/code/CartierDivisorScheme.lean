/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.GroupTheory.QuotientGroup.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace CartierDivisorScheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The natural map from units of the structure sheaf on `U` to units of the function field of an
integral scheme, induced by the germ-to-function-field morphism. -/
noncomputable def structureUnitsToFunctionFieldUnits (U : X.Opens) [Nonempty U] :
    Γ(X, U)ˣ →* (X.functionField)ˣ :=
  Units.map (X.germToFunctionField U).hom.toMonoidHom

/-- The image inside `(X.functionField)ˣ` of the units of the structure sheaf on `U`. -/
noncomputable def structureUnitsSubgroup (U : X.Opens) [Nonempty U] :
    Subgroup (X.functionField)ˣ :=
  (structureUnitsToFunctionFieldUnits X U).range

/-- The Cartier divisor presheaf on `U` defined as the quotient `K(X)ˣ / O(U)ˣ`, modelling
sections of `K*/O*`. -/
noncomputable def CartierDivisorPresheafQuotient (U : X.Opens) [Nonempty U] : Type u :=
  (X.functionField)ˣ ⧸ structureUnitsSubgroup X U

end CartierDivisorScheme
