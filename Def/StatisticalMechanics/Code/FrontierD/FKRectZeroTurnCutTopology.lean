module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
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

def FKRectMedialHitsHorizontalSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) : Prop :=
  ∃ i : Fin R.medialTorus.width,
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkMedialVerticalSeamDart R.medialTorus i) = C


end
end StatMech.FrontierD
