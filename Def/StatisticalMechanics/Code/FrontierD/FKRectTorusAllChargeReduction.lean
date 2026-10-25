/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSignedChargeBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
open Matrix


namespace StatMech.FrontierD

noncomputable section

def fkRectFixedChargeSector (R : FKRectTorus) (r : Nat)
    (_hr : r <= R.medialTorus.width / 2) :
    Fin (R.medialTorus.width + 1) :=
  ⟨R.medialTorus.width / 2 - r,
    Nat.lt_succ_of_le
      ((Nat.sub_le _ _).trans
        (Nat.div_le_self R.medialTorus.width 2))⟩


def fkRectFixedChargeTilt (R : FKRectTorus) (q lam : Real)
    (r : Nat) (hr : r <= R.medialTorus.width / 2)
    (omega : R.Configuration) : Real :=
  fkRectSignedChargeTilt R q lam (fkRectFixedChargeSector R r hr) omega


def fkRectVerticalFluxTilt (R : FKRectTorus) (q lam : Real)
    (z : Int) (omega : R.Configuration) : Real :=
  (∑ arrows : SixVertexArrows R.medialTorus,
      if fkOrientedLoopVerticalFlux R.medialTorus arrows = z then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0) /
    fkRectCriticalReducedWeight R q omega


end
end StatMech.FrontierD
