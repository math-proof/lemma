/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part3
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectFixedChargeFreeOneArm
    {q : Real} (hq : 1 ≤ q) (r k : Nat) : Real :=
  (FK.freeInfiniteVolume 2
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
      (zero_lt_one.trans_le hq) :
    MeasureTheory.Measure (ConfigSpace
      (Sym2 (StatMech.Lattice.Site 2)))).real
    (FK.boxBdryConnEvent 2
      ((fkRectFixedChargeVerticalFamily r k 0).width - 2))


noncomputable def fkRectBoundaryIncidencePIMSHeightLower
    (q : Real) (r k : Nat) : Nat :=
  let width := (fkRectFixedChargeVerticalFamily r k 0).width
  k * width + fkRectPIMSHeightLower (FK.cFE (fkRectCriticalP q) q) width


end
end StatMech.FrontierD
