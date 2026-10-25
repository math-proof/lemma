/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


namespace HexFiniteRegion

variable (R : HexFiniteRegion)


variable {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def supportFinset (hdu : du ≠ 0) : Finset (List ℤ) :=
  (R.support_finite (a := a) (h0 := h0) (v := v) (du := du) hdu).toFinset


end HexFiniteRegion
end StatMech.Universality
