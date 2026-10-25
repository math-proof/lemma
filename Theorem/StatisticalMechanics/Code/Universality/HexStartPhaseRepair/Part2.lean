/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
import Def.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexFiniteStripBoundaryCore

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing}


theorem Fa_eq_hexChi (C : HexFiniteStripBoundaryCore R h0 D P) :
    C.Fa = hexChi := by
  apply Complex.ofReal_injective
  calc
    (C.Fa : ℂ) = D.obs R.start := C.Fa_eq
    _ = parafObservable R.inRegion R.start h0 R.start (5 / 8) hexChi :=
      C.obs_eq R.start
    _ = (hexChi : ℂ) :=
      parafObservable_start_eq_weight_of_unique
        R.inRegion R.start h0 (5 / 8) hexChi
        (by simpa [HexFiniteRegion.inRegion] using R.start_mem)
        (by
          intro ts hts
          exact hexReturningLegalSAW_eq_nil R.start h0 ts hts.1 hts.2.2)

@[simp] theorem ofBoundaryData_Fa
    (B : HexFiniteStripBoundaryData R h0 D P) :
    (ofBoundaryData B).Fa = B.Fa := rfl

end HexFiniteStripBoundaryCore
end StatMech.Universality
