module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectWiredDualAddedEdges
    (R : FKRectTorus) (omega : R.Configuration) : Finset R.EdgeIndex :=
  fkRectDualCutEdges R \
    fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega)

end
end StatMech.FrontierD
