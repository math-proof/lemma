module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetNormalization
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectAllSectorNormalization (R : FKRectTorus) (q : Real) : Real :=
  Real.sqrt q ^ (R.width * R.height : Nat) *
    (sixVertexTorusArrowPartitionSum R.medialTorus
        (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q)


end
end StatMech.FrontierD
