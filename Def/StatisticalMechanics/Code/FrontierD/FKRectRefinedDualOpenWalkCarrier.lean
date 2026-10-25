/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualOpenWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualEdgeCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedPathReversal


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedDualScalePoint (p : Int × Int) : Int × Int :=
  (4 * p.1 + 2, 4 * p.2 + 2)


end
end StatMech.FrontierD
