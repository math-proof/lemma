/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectWiredDualAddedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) : List R.EdgeIndex :=
  (fkRectWiredDualAddedEdges R omega).toList

end
end StatMech.FrontierD
