/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectDualCutEdges (R : FKRectTorus) : Finset R.EdgeIndex :=
  (fkRectTorusCutEdges R).image (fkRectEdgeToDualEdge R)

end
end StatMech.FrontierD
