/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators

namespace HexFiniteRegion

variable (R : HexFiniteRegion) {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def hxv_supportVertices (hdu : du ≠ 0) : Finset ℂ :=
  (R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu).biUnion
    (fun ts => (ofTurns a h0 ts).vertices.toFinset)


end HexFiniteRegion
end StatMech.Universality
