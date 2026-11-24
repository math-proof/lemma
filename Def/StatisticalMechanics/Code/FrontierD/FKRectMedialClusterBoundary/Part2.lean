module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialReachability
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonReduction
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClusterBoundary
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectMedialComponentToPrimalComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).ConnectedComponent ->
      (fkRectOpenGraph R omega).ConnectedComponent :=
  ConnectedComponent.lift
    (fun d => (fkRectOpenGraph R omega).connectedComponentMk
      (fkRectMedialDartPrimalLabel R d))
    (by
      intro d e p hp
      apply ConnectedComponent.sound
      exact fkRectMedial_reachable_primalLabel_reachable R omega ⟨p⟩)

end
end StatMech.FrontierD
