module
public import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectDualEvent (R : FKRectTorus)
    (A : Set R.Configuration) : Set R.Configuration :=
  fkRectDualConfigurationEquiv R '' A


def fkRectDualPreimageEvent (R : FKRectTorus)
    (A : Set R.Configuration) : Set R.Configuration :=
  fkRectDualConfigurationEquiv R ⁻¹' A

end
end StatMech.FrontierD
