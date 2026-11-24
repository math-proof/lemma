module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection.Part4
open MeasureTheory SimpleGraph StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalStablePairedWitnessCore
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (eta : R.Configuration) : Prop :=
  FKRectPrimalFullDistinctPairedWitness R pair S
    (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))

end
end StatMech.FrontierD
