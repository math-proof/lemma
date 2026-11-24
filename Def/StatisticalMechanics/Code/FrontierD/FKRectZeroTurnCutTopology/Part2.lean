module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutTopology
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectMedialHorizontalSeamComponents
    (R : FKRectTorus) (omega : R.Configuration) :
    Finset (FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) := by
  classical
  exact Finset.univ.filter fun C =>
    FKRectMedialHitsHorizontalSeam R omega C

end
end StatMech.FrontierD
