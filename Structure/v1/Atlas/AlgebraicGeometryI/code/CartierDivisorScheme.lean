/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.GroupTheory.QuotientGroup.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace CartierDivisorScheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- A Cartier divisor datum on `X` (Def 31, Lec 15): a cover of `X` by open sets `Uᵢ`, rational
functions `fᵢ ∈ K(X)ˣ`, and the compatibility `f_j · f_i⁻¹` is a unit of `O(U_i ∩ U_j)` on
overlaps. -/
structure CartierDivisorDatum where
  ι : Type u
  cover : ι → X.Opens
  cover_eq_top : ⨆ i, cover i = ⊤
  f : ι → (X.functionField)ˣ
  compat : ∀ (i j : ι) (h : Nonempty (cover i ⊓ cover j : X.Opens)),
    f j * (f i)⁻¹ ∈
      (@structureUnitsToFunctionFieldUnits X _ (cover i ⊓ cover j) h).range

end CartierDivisorScheme
