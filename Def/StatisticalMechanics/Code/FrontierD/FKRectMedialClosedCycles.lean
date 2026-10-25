/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles
open Equiv


namespace StatMech.FrontierD

def fkRectFullMedialPairing (R : FKRectTorus) :
    FKMedialLoopPairing R.medialTorus :=
  fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R Finset.univ)

end StatMech.FrontierD
