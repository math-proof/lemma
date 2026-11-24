module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedEdgeCenterClass
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurnWalk.Part2
public import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectBlackDartShiftedSite_zero
    (R : FKRectTorus) (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackDartShiftedSite R (0, 0) d =
      fkRectBlackDartSite R d := by
  simp [fkRectBlackDartShiftedSite, fkRectBlackDartSite,
    fkRectBlackDartShiftedPoint, fkRectSquareDeckTranslation]

end
end StatMech.FrontierD
