/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace CartierDivisorScheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The Cartier divisor group on a scheme `X`, modelled as the type of `CartierDivisorDatum`. -/
def CartierDivisorGroupScheme : Type _ := CartierDivisorDatum X

end CartierDivisorScheme
