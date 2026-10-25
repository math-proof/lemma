/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.BoolModeForcedSum
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
import Instance.StatisticalMechanics.Code.FrontierD.FKRectChargeOneModeComparison
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectComponentModeWeight {T : EvenTorus}
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (C : FKMedialLoop T pairing) (b : Bool) : Real :=
  if b then
    Real.exp (-(lam / 4) *
      FKMedialTurningFiber.canonicalComponentTurn pairing C)
  else
    Real.exp ((lam / 4) *
      FKMedialTurningFiber.canonicalComponentTurn pairing C)


def fkRectChargeOneModeCost (lam : Real) : Real :=
  1 + Real.exp (2 * lam)

end
end StatMech.FrontierD
