module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialReachability
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBoundaryWalk.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectMedialBoundaryPrimalStepWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d)) := by
  classical
  by_cases heq : fkRectMedialDartPrimalLabel R d =
      fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d)
  · exact (.nil : (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R d)).copy rfl heq
  · exact .cons
      ((fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj R omega d).resolve_left heq)
      .nil

end
end StatMech.FrontierD
