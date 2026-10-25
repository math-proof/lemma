/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part8


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def hexPBaseTurns (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) : Finset (List ℤ) := by
  classical
  exact
    (R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu).filter
      (fun ts => (ofTurns a h0 ts).EndsAt (v + du))


def hexPBaseIndices (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) : Finset ℕ :=
  (hexPBaseTurns R a h0 v du hdu).image Encodable.encode


end
end StatMech.Universality
