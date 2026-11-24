module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part5
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectHorizontalCylinderStablePairedWitnessCore
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width)) (eta : R.Configuration) : Prop :=
  FKRectHorizontalCylinderDistinctPairedWitness R pair S
    (fkRectFullGraphConfiguration R
      (fkRectForceHorizontalCutClosed R eta))

end
end StatMech.FrontierD
